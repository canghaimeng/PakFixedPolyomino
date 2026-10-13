import PakFixedPolyomino.MStarConcreteAlphabet
import Mathlib.Tactic

/-!
# Backward soundness infrastructure for the concrete `M_star` parser

The forward trace proves that every `encodedWord` reaches `copyReady`.  This
module develops the converse directly against the executable zipper
semantics.  `CanAcceptResult` is deliberately defined from `run`; it is not a
replacement specification.  The one-step equivalence below lets each parser
clause be inverted without choosing a particular fuel witness.
-/

namespace PakFixedPolyomino.MStarParserSoundness

open MStarOuterProgram MStarParserMicrocode MStarParserExecution
open MStarConcreteAlphabet

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

def CanAcceptResult (r : Result MStarConcreteAlphabet.CoreTape) : Prop :=
  ∃ fuel z, run zero one work fuel r = .copyReady z

theorem canAcceptResult_oneStep_iff
    (r : Result MStarConcreteAlphabet.CoreTape) :
    CanAcceptResult (oneStep zero one work r) ↔ CanAcceptResult r := by
  constructor
  · rintro ⟨fuel, z, h⟩
    exact ⟨fuel + 1, z, by simpa [run]⟩
  · rintro ⟨fuel, z, h⟩
    cases fuel with
    | zero =>
        simp only [run] at h
        subst r
        exact ⟨0, z, rfl⟩
    | succ fuel =>
        exact ⟨fuel, z, h⟩

theorem canAcceptResult_run_iff (fuel : ℕ)
    (r : Result MStarConcreteAlphabet.CoreTape) :
    CanAcceptResult (run zero one work fuel r) ↔ CanAcceptResult r := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
      rw [run_succ, ih]
      exact canAcceptResult_oneStep_iff r

@[simp] theorem canAcceptResult_copyReady
    (z : Zipper (Tape MStarConcreteAlphabet.CoreTape)) :
    CanAcceptResult (.copyReady z) := ⟨0, z, rfl⟩

@[simp] theorem not_canAcceptResult_rejected :
    ¬ CanAcceptResult (.rejected : Result MStarConcreteAlphabet.CoreTape) := by
  rintro ⟨fuel, z, h⟩
  rw [result_absorbing_rejected] at h
  contradiction

@[simp] theorem not_canAcceptResult_stuck :
    ¬ CanAcceptResult (.stuck : Result MStarConcreteAlphabet.CoreTape) := by
  rintro ⟨fuel, z, h⟩
  rw [result_absorbing_stuck] at h
  contradiction

theorem canAcceptResult_of_reaches {r s : Result MStarConcreteAlphabet.CoreTape}
    (hrs : Reaches zero one work r s) (hs : CanAcceptResult s) :
    CanAcceptResult r := by
  rcases hrs with ⟨a, ha⟩
  rcases hs with ⟨b, z, hb⟩
  exact ⟨a + b, z, by rw [run_add, ha, hb]⟩

theorem canAcceptResult_reaches_forward {r s : Result CoreTape}
    (hrs : Reaches zero one work r s) (hr : CanAcceptResult r) :
    CanAcceptResult s := by
  rcases hrs with ⟨fuel, hrun⟩
  have hafter := (canAcceptResult_run_iff fuel r).2 hr
  rw [hrun] at hafter
  exact hafter

theorem parserAccepts_iff_canAcceptResult (w : ConcretePakSide.Word) :
    Accepts zero one work w ↔
      CanAcceptResult (initial zero one work w) := Iff.rfl

/-- Any successful execution has exactly one final zipper, independently of
the amount of fuel used to witness success. -/
theorem successful_output_unique (w : ConcretePakSide.Word)
    (fuel₁ fuel₂ : ℕ)
    (z₁ z₂ : Zipper (Tape MStarConcreteAlphabet.CoreTape))
    (h₁ : run zero one work fuel₁ (initial zero one work w) = .copyReady z₁)
    (h₂ : run zero one work fuel₂ (initial zero one work w) = .copyReady z₂) :
    z₁ = z₂ :=
  copyReady_output_unique zero one work _ fuel₁ fuel₂ z₁ z₂ h₁ h₂

@[simp] theorem fixed_ne_copyStart (k : Fin 73) : fixed k ≠ copyStart := by
  change (Sum.inl (Sum.inl k) : ParserState) ≠ Sum.inr _
  exact Sum.inl_ne_inr

theorem parserStep_fixed_zero (k : Fin 73) (hk : k.1 < 72) :
    MStarParserMicrocode.step (UState := Unit) zero one work (fixed k) (.core zero) =
      some (MStarParserMicrocode.go
        (if k.1 = 0 then endpointMark else padDone)
        (fixed (MStarParserMicrocode.next73 k hk)) .right) := by
  unfold MStarParserMicrocode.step
  change (if hfix : k.1 < 73 then _ else _) = _
  rw [dif_pos k.isLt]
  change (if hk' : k.1 < 72 then _ else _) = _
  rw [dif_pos hk]
  simp only [MStarParserMicrocode.coreEq,
    MStarConcreteAlphabet.parser_coreEq_zero, if_true]
  congr 3

theorem parserStep_fixed_wrong_core (k : Fin 73) (hk : k.1 < 72)
    (a : CoreTape) (ha : a ≠ zero) :
    MStarParserMicrocode.step (UState := Unit) zero one work (fixed k) (.core a) =
      some (MStarParserMicrocode.reject (.core a)) := by
  unfold MStarParserMicrocode.step
  change (if hfix : k.1 < 73 then _ else _) = _
  rw [dif_pos k.isLt]
  change (if hk' : k.1 < 72 then _ else _) = _
  rw [dif_pos hk]
  simp [MStarParserMicrocode.coreEq, ha]

theorem oneStep_fixed_zero_nil (k : Fin 73) (hk : k.1 < 72)
    (left : List (Tape MStarConcreteAlphabet.CoreTape)) :
    oneStep zero one work (.running (fixed k) ⟨left, .core zero, []⟩) =
      .stuck := by
  unfold oneStep
  change (if fixed k = copyStart then _ else _) = _
  rw [if_neg (fixed_ne_copyStart k)]
  rw [parserStep_fixed_zero k hk]
  rfl

theorem oneStep_fixed_zero_cons (k : Fin 73) (hk : k.1 < 72)
    (left : List (Tape MStarConcreteAlphabet.CoreTape))
    (y : Tape MStarConcreteAlphabet.CoreTape)
    (right : List (Tape MStarConcreteAlphabet.CoreTape)) :
    oneStep zero one work
      (.running (fixed k) ⟨left, .core zero, y :: right⟩) =
      .running (fixed (MStarParserMicrocode.next73 k hk))
        ⟨(if k.1 = 0 then endpointMark else padDone) :: left, y, right⟩ := by
  unfold oneStep
  change (if fixed k = copyStart then _ else _) = _
  rw [if_neg (fixed_ne_copyStart k)]
  rw [parserStep_fixed_zero k hk]
  rfl

theorem oneStep_fixed_wrong_core (k : Fin 73) (hk : k.1 < 72)
    (left right : List (Tape MStarConcreteAlphabet.CoreTape))
    (a : MStarConcreteAlphabet.CoreTape) (ha : a ≠ zero) :
    oneStep zero one work (.running (fixed k) ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if fixed k = copyStart then _ else _) = _
  rw [if_neg (fixed_ne_copyStart k)]
  rw [parserStep_fixed_wrong_core k hk a ha]
  rfl

theorem oneStep_fixed_noncore (k : Fin 73) (hk : k.1 < 72)
    (left right : List (Tape MStarConcreteAlphabet.CoreTape))
    (x : Tape MStarConcreteAlphabet.CoreTape)
    (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running (fixed k) ⟨left, x, right⟩) =
      .rejected := by
  have hp : MStarParserMicrocode.step (UState := Unit) zero one work
      (fixed k) x = some (MStarParserMicrocode.reject x) := by
    cases x with
    | core a => exact (hx a rfl).elim
    | hash | markL | markR | scratch =>
        unfold MStarParserMicrocode.step
        change (if hfix : k.1 < 73 then _ else _) = _
        rw [dif_pos k.isLt]
        change (if hk' : k.1 < 72 then _ else _) = _
        rw [dif_pos hk]
  cases x with
  | core a => exact (hx a rfl).elim
  | hash | markL | markR | scratch =>
      unfold oneStep
      change (if fixed k = copyStart then _ else _) = _
      rw [if_neg (fixed_ne_copyStart k)]
      rw [hp]
      simp [MStarParserMicrocode.reject, applyAction]

/-- A successful run cannot pass a fixed-prefix counter state unless the
current cell is the concrete zero letter and a target cell exists to its
right.  This is the first backward clause of the parser-language proof. -/
theorem fixed_canAccept_forces_zero_and_right (k : Fin 73) (hk : k.1 < 72)
    (z : Zipper (Tape MStarConcreteAlphabet.CoreTape))
    (hacc : CanAcceptResult (.running (fixed k) z)) :
    z.focus = .core zero ∧ z.right ≠ [] := by
  rcases z with ⟨left, focus, right⟩
  have hnext : CanAcceptResult
      (oneStep zero one work (.running (fixed k) ⟨left, focus, right⟩)) :=
    (canAcceptResult_oneStep_iff _).2 hacc
  cases focus with
  | core a =>
      by_cases ha : a = zero
      · subst a
        refine ⟨rfl, ?_⟩
        intro hr
        change right = [] at hr
        subst right
        have hstep := oneStep_fixed_zero_nil k hk left
        rw [hstep] at hnext
        exact not_canAcceptResult_stuck hnext
      · have hstep : oneStep zero one work
            (.running (fixed k) ⟨left, .core a, right⟩) = .rejected := by
          exact oneStep_fixed_wrong_core k hk left right a ha
        rw [hstep] at hnext
        exact (not_canAcceptResult_rejected hnext).elim
  | hash =>
      have hstep : oneStep zero one work
          (.running (fixed k) ⟨left, .hash, right⟩) = .rejected := by
        exact oneStep_fixed_noncore k hk left right .hash (by simp)
      rw [hstep] at hnext
      exact (not_canAcceptResult_rejected hnext).elim
  | markL =>
      have hstep : oneStep zero one work
          (.running (fixed k) ⟨left, .markL, right⟩) = .rejected := by
        exact oneStep_fixed_noncore k hk left right .markL (by simp)
      rw [hstep] at hnext
      exact (not_canAcceptResult_rejected hnext).elim
  | markR =>
      have hstep : oneStep zero one work
          (.running (fixed k) ⟨left, .markR, right⟩) = .rejected := by
        exact oneStep_fixed_noncore k hk left right .markR (by simp)
      rw [hstep] at hnext
      exact (not_canAcceptResult_rejected hnext).elim
  | scratch i =>
      have hstep : oneStep zero one work
          (.running (fixed k) ⟨left, .scratch i, right⟩) = .rejected := by
        exact oneStep_fixed_noncore k hk left right (.scratch i) (by simp)
      rw [hstep] at hnext
      exact (not_canAcceptResult_rejected hnext).elim

theorem fixed_canAccept_forces_zero_prefix (k : Fin 73) (n : ℕ)
    (hbound : k.1 + n ≤ 72)
    (z : Zipper (Tape MStarConcreteAlphabet.CoreTape))
    (hacc : CanAcceptResult (.running (fixed k) z)) :
    (z.focus :: z.right).take n =
      List.replicate n (Tape.core zero) := by
  induction n generalizing k z with
  | zero => rfl
  | succ n ih =>
      have hk : k.1 < 72 := by omega
      rcases fixed_canAccept_forces_zero_and_right k hk z hacc with
        ⟨hzero, hright⟩
      rcases z with ⟨left, focus, right⟩
      change focus = .core zero at hzero
      subst focus
      cases hrightList : right with
      | nil =>
          exact (hright hrightList).elim
      | cons y ys =>
          subst right
          have hnext : CanAcceptResult
              (oneStep zero one work
                (.running (fixed k) ⟨left, .core zero, y :: ys⟩)) :=
            (canAcceptResult_oneStep_iff _).2 hacc
          rw [oneStep_fixed_zero_cons k hk] at hnext
          have hbound' : (MStarParserMicrocode.next73 k hk).1 + n ≤ 72 := by
            simp [MStarParserMicrocode.next73]
            omega
          have htail := ih (MStarParserMicrocode.next73 k hk) hbound'
            ⟨(if k.1 = 0 then endpointMark else padDone) :: left, y, ys⟩ hnext
          simpa [List.take, List.replicate_succ] using
            congrArg (fun xs => Tape.core zero :: xs) htail

theorem fixed_canAccept_forces_room (k : Fin 73) (n : ℕ)
    (hbound : k.1 + n ≤ 72)
    (z : Zipper (Tape MStarConcreteAlphabet.CoreTape))
    (hacc : CanAcceptResult (.running (fixed k) z)) :
    n < (z.focus :: z.right).length := by
  induction n generalizing k z with
  | zero => simp
  | succ n ih =>
      have hk : k.1 < 72 := by omega
      rcases fixed_canAccept_forces_zero_and_right k hk z hacc with
        ⟨hzero, hright⟩
      rcases z with ⟨left, focus, right⟩
      change focus = .core zero at hzero
      subst focus
      cases hrightList : right with
      | nil => exact (hright hrightList).elim
      | cons y ys =>
          subst right
          have hnext : CanAcceptResult
              (oneStep zero one work
                (.running (fixed k) ⟨left, .core zero, y :: ys⟩)) :=
            (canAcceptResult_oneStep_iff _).2 hacc
          rw [oneStep_fixed_zero_cons k hk] at hnext
          have hbound' : (MStarParserMicrocode.next73 k hk).1 + n ≤ 72 := by
            simp [MStarParserMicrocode.next73]
            omega
          have htail := ih (MStarParserMicrocode.next73 k hk) hbound'
            ⟨(if k.1 = 0 then endpointMark else padDone) :: left, y, ys⟩ hnext
          have htail' : n < (y :: ys).length := by
            simpa using htail
          simp only [List.length_cons] at htail' ⊢
          omega

theorem parserAccepts_forces_fixed_zero_prefix (w : ConcretePakSide.Word)
    (hacc : Accepts zero one work w) :
    (inputCells zero one work w).take 72 =
      List.replicate 72 (Tape.core zero) := by
  have hcan : CanAcceptResult (initial zero one work w) := hacc
  cases hcells : inputCells zero one work w with
  | nil => exact (inputCells_ne_nil zero one work w hcells).elim
  | cons y ys =>
      have hrun : initial zero one work w =
          .running (fixed 0) ⟨[], y, ys⟩ := by
        unfold initial
        rw [hcells]
      rw [hrun] at hcan
      have hprefix := fixed_canAccept_forces_zero_prefix
        (0 : Fin 73) 72 (by decide) ⟨[], y, ys⟩ hcan
      simpa [hcells] using hprefix

theorem bitCell_injective :
    Function.Injective (bitCell zero one) := by
  intro a b
  cases a <;> cases b <;> native_decide

theorem parserAccepts_forces_padding_suffix (w : ConcretePakSide.Word)
    (hacc : Accepts zero one work w) :
    72 ≤ w.length ∧
      w.reverse.take 72 = List.replicate 72 false := by
  have hcan : CanAcceptResult (initial zero one work w) := hacc
  have hprefix := parserAccepts_forces_fixed_zero_prefix w hacc
  have hroom : 72 < (inputCells zero one work w).length := by
    cases hcells : inputCells zero one work w with
    | nil => exact (inputCells_ne_nil zero one work w hcells).elim
    | cons y ys =>
        have hrun : initial zero one work w =
            .running (fixed 0) ⟨[], y, ys⟩ := by
          unfold initial
          rw [hcells]
        rw [hrun] at hcan
        have hr := fixed_canAccept_forces_room
          (0 : Fin 73) 72 (by decide) ⟨[], y, ys⟩ hcan
        simpa [hcells] using hr
  have hwlen : 72 ≤ w.length := by
    simp [inputCells] at hroom
    omega
  refine ⟨hwlen, ?_⟩
  have hmaplen : 72 ≤
      (w.reverse.map (bitCell zero one)).length := by
    simpa using hwlen
  have hprefix' :
      (w.reverse.map (bitCell zero one)).take 72 =
        List.replicate 72 (Tape.core zero) := by
    rw [show inputCells zero one work w =
      w.reverse.map (bitCell zero one) ++ [.core work] by rfl] at hprefix
    rw [List.take_append_of_le_length hmaplen] at hprefix
    exact hprefix
  have hmapped : (w.reverse.take 72).map (bitCell zero one) =
      List.replicate 72 (Tape.core zero) := by
    simpa only [List.map_take] using hprefix'
  have hrhs : List.replicate 72 (Tape.core zero) =
      (List.replicate 72 false).map (bitCell zero one) := by
    simp [bitCell]
  rw [hrhs] at hmapped
  exact (List.map_injective_iff.mpr bitCell_injective) hmapped

theorem parserAccepts_after_fixed_prefix (w : ConcretePakSide.Word)
    (hacc : Accepts zero one work w) :
    ∃ y ys,
      inputCells zero one work w =
        List.replicate 72 (Tape.core zero) ++ y :: ys ∧
      CanAcceptResult
        (.running scanPad ⟨fixedPaddingTail, y, ys⟩) := by
  let cells := inputCells zero one work w
  have hcan : CanAcceptResult (initial zero one work w) := hacc
  have hprefix : cells.take 72 =
      List.replicate 72 (Tape.core zero) := by
    exact parserAccepts_forces_fixed_zero_prefix w hacc
  have hroom : 72 < cells.length := by
    have hw := (parserAccepts_forces_padding_suffix w hacc).1
    simp [cells, inputCells]
    omega
  have hdrop : cells.drop 72 ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
    omega
  cases htail : cells.drop 72 with
  | nil => exact (hdrop htail).elim
  | cons y ys =>
      have hshape : cells =
          List.replicate 72 (Tape.core zero) ++ y :: ys := by
        calc
          cells = cells.take 72 ++ cells.drop 72 :=
            (List.take_append_drop 72 cells).symm
          _ = List.replicate 72 (Tape.core zero) ++ y :: ys := by
            rw [hprefix, htail]
      have hstart : initial zero one work w =
          .running (fixed 0)
            ⟨[], .core zero, List.replicate 71 (.core zero) ++ y :: ys⟩ := by
        unfold initial
        rw [show inputCells zero one work w = cells by rfl, hshape]
        simp [List.replicate_succ, List.append_assoc]
      have hfixed : CanAcceptResult
          (.running (fixed ⟨72, by decide⟩)
            ⟨fixedPaddingTail, y, ys⟩) := by
        have hafter :=
          (canAcceptResult_run_iff 72 (initial zero one work w)).2 hcan
        rw [hstart] at hafter
        rw [run_fixed_72 y ys] at hafter
        exact hafter
      have hscan : CanAcceptResult
          (oneStep zero one work
            (.running (fixed ⟨72, by decide⟩)
              ⟨fixedPaddingTail, y, ys⟩)) :=
        (canAcceptResult_oneStep_iff _).2 hfixed
      have hstep : oneStep zero one work
          (.running (fixed ⟨72, by decide⟩)
            ⟨fixedPaddingTail, y, ys⟩) =
          .running scanPad ⟨fixedPaddingTail, y, ys⟩ :=
        oneStep_fixed_72 _
      rw [hstep] at hscan
      exact ⟨y, ys, hshape, hscan⟩

@[simp] theorem scanPad_ne_copyStart : scanPad ≠ copyStart := by
  native_decide

theorem parserStep_scanPad_core (a : CoreTape) :
    MStarParserMicrocode.step (UState := Unit) zero one work scanPad (.core a) =
      if MStarParserMicrocode.coreEq a zero then
        some (MStarParserMicrocode.go (.core a) scanPad .right)
      else if MStarParserMicrocode.coreEq a one then
        some (MStarParserMicrocode.go sepPad scanLen .right)
      else some (MStarParserMicrocode.reject (.core a)) := by
  rfl

theorem parserStep_scanPad_noncore
    (x : Tape CoreTape) (hx : ∀ a, x ≠ .core a) :
    MStarParserMicrocode.step (UState := Unit) zero one work scanPad x =
      some (MStarParserMicrocode.reject x) := by
  cases x with
  | core a => exact (hx a rfl).elim
  | hash | markL | markR | scratch => rfl

theorem oneStep_scanPad_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape)
    (hz : a ≠ zero) (ho : a ≠ one) :
    oneStep zero one work (.running scanPad ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if scanPad = copyStart then _ else _) = _
  rw [if_neg scanPad_ne_copyStart, parserStep_scanPad_core]
  simp [MStarParserMicrocode.coreEq, hz, ho,
    MStarParserMicrocode.reject, applyAction]

theorem oneStep_scanPad_noncore
    (left right : List (Tape CoreTape)) (x : Tape CoreTape)
    (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running scanPad ⟨left, x, right⟩) =
      .rejected := by
  unfold oneStep
  change (if scanPad = copyStart then _ else _) = _
  rw [if_neg scanPad_ne_copyStart, parserStep_scanPad_noncore x hx]
  simp [MStarParserMicrocode.reject, applyAction]

theorem oneStep_scanPad_zero_nil (left : List (Tape CoreTape)) :
    oneStep zero one work (.running scanPad ⟨left, .core zero, []⟩) =
      .stuck := by
  rfl

theorem oneStep_scanPad_one_nil (left : List (Tape CoreTape)) :
    oneStep zero one work (.running scanPad ⟨left, .core one, []⟩) =
      .stuck := by
  rfl

theorem scanPad_canAccept_split
    (left : List (Tape CoreTape)) (focus : Tape CoreTape)
    (right : List (Tape CoreTape))
    (hacc : CanAcceptResult (.running scanPad ⟨left, focus, right⟩)) :
    ∃ n y ys,
      focus :: right =
        List.replicate n (Tape.core zero) ++ Tape.core one :: y :: ys ∧
      CanAcceptResult
        (.running scanLen
          ⟨sepPad :: List.replicate n (Tape.core zero) ++ left, y, ys⟩) := by
  induction right generalizing left focus with
  | nil =>
      have hnext := (canAcceptResult_oneStep_iff _).2 hacc
      cases focus with
      | core a =>
          by_cases hz : a = zero
          · subst a
            rw [oneStep_scanPad_zero_nil] at hnext
            exact (not_canAcceptResult_stuck hnext).elim
          · by_cases ho : a = one
            · subst a
              rw [oneStep_scanPad_one_nil] at hnext
              exact (not_canAcceptResult_stuck hnext).elim
            · rw [oneStep_scanPad_wrong_core _ _ _ hz ho] at hnext
              exact (not_canAcceptResult_rejected hnext).elim
      | hash =>
          rw [oneStep_scanPad_noncore _ _ .hash (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markL =>
          rw [oneStep_scanPad_noncore _ _ .markL (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markR =>
          rw [oneStep_scanPad_noncore _ _ .markR (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | scratch i =>
          rw [oneStep_scanPad_noncore _ _ (.scratch i) (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
  | cons y ys ih =>
      have hnext := (canAcceptResult_oneStep_iff _).2 hacc
      cases focus with
      | core a =>
          by_cases hz : a = zero
          · subst a
            rw [MStarConcreteAlphabet.oneStep_scanPad_zero] at hnext
            rcases ih (Tape.core zero :: left) y hnext with
              ⟨n, z, zs, hshape, hfinal⟩
            refine ⟨n + 1, z, zs, ?_, ?_⟩
            · simp [hshape, List.replicate_succ, List.append_assoc]
            · simpa [List.replicate_succ, replicate_cons_rotate,
                List.append_assoc] using hfinal
          · by_cases ho : a = one
            · subst a
              rw [MStarConcreteAlphabet.oneStep_scanPad_separator] at hnext
              exact ⟨0, y, ys, rfl, hnext⟩
            · rw [oneStep_scanPad_wrong_core _ _ _ hz ho] at hnext
              exact (not_canAcceptResult_rejected hnext).elim
      | hash =>
          rw [oneStep_scanPad_noncore _ _ .hash (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markL =>
          rw [oneStep_scanPad_noncore _ _ .markL (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markR =>
          rw [oneStep_scanPad_noncore _ _ .markR (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | scratch i =>
          rw [oneStep_scanPad_noncore _ _ (.scratch i) (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim

theorem parserAccepts_after_scanPad (w : ConcretePakSide.Word)
    (hacc : Accepts zero one work w) :
    ∃ padding y ys,
      inputCells zero one work w =
        List.replicate 72 (Tape.core zero) ++
          List.replicate padding (Tape.core zero) ++ Tape.core one :: y :: ys ∧
      CanAcceptResult
        (.running scanLen
          ⟨sepPad :: List.replicate padding (Tape.core zero) ++ fixedPaddingTail,
            y, ys⟩) := by
  rcases parserAccepts_after_fixed_prefix w hacc with
    ⟨focus, right, hinput, hscan⟩
  rcases scanPad_canAccept_split fixedPaddingTail focus right hscan with
    ⟨padding, y, ys, hshape, hlen⟩
  refine ⟨padding, y, ys, ?_, ?_⟩
  · rw [hinput, hshape]
    simp [List.append_assoc]
  · exact hlen

@[simp] theorem cross_ne_copyStart (k : Fin 73) : cross k ≠ copyStart := by
  change (Sum.inl (Sum.inr k) : ParserState) ≠ Sum.inr _
  exact Sum.inl_ne_inr

theorem parserStep_cross_zero (k : Fin 73) (hk : k.1 < 72) :
    MStarParserMicrocode.step (UState := Unit) zero one work (cross k) (.core zero) =
      some (MStarParserMicrocode.go padDone
        (cross (MStarParserMicrocode.next73 k hk)) .left) := by
  unfold MStarParserMicrocode.step
  change (if hfix : 73 + k.1 < 73 then _ else _) = _
  rw [dif_neg (by omega)]
  change (if hcross : 73 + k.1 < 146 then _ else _) = _
  rw [dif_pos (by omega)]
  simp only [MStarParserMicrocode.stateCode, MStarParserMicrocode.cross,
    Nat.add_sub_cancel_left]
  change (if hk' : k.1 < 72 then _ else _) = _
  rw [dif_pos hk]
  simp only [MStarParserMicrocode.coreEq,
    MStarConcreteAlphabet.parser_coreEq_zero, if_true]
  congr 3

theorem parserStep_cross_wrong_core (k : Fin 73) (hk : k.1 < 72)
    (a : CoreTape) (ha : a ≠ zero) :
    MStarParserMicrocode.step (UState := Unit) zero one work (cross k) (.core a) =
      some (MStarParserMicrocode.reject (.core a)) := by
  unfold MStarParserMicrocode.step
  change (if hfix : 73 + k.1 < 73 then _ else _) = _
  rw [dif_neg (by omega)]
  change (if hcross : 73 + k.1 < 146 then _ else _) = _
  rw [dif_pos (by omega)]
  simp only [MStarParserMicrocode.stateCode, MStarParserMicrocode.cross,
    Nat.add_sub_cancel_left]
  change (if hk' : k.1 < 72 then _ else _) = _
  rw [dif_pos hk]
  simp [MStarParserMicrocode.coreEq, ha]

theorem parserStep_cross_noncore (k : Fin 73) (hk : k.1 < 72)
    (x : Tape CoreTape) (hx : ∀ a, x ≠ .core a) :
    MStarParserMicrocode.step (UState := Unit) zero one work (cross k) x =
      some (MStarParserMicrocode.reject x) := by
  cases x with
  | core a => exact (hx a rfl).elim
  | hash | markL | markR | scratch =>
      unfold MStarParserMicrocode.step
      change (if hfix : 73 + k.1 < 73 then _ else _) = _
      rw [dif_neg (by omega)]
      change (if hcross : 73 + k.1 < 146 then _ else _) = _
      rw [dif_pos (by omega)]
      simp only [MStarParserMicrocode.stateCode, MStarParserMicrocode.cross,
        Nat.add_sub_cancel_left]
      change (if hk' : k.1 < 72 then _ else _) = _
      rw [dif_pos hk]

theorem oneStep_cross_zero_nil (k : Fin 73) (hk : k.1 < 72)
    (right : List (Tape CoreTape)) :
    oneStep zero one work (.running (cross k) ⟨[], .core zero, right⟩) =
      .stuck := by
  unfold oneStep
  change (if cross k = copyStart then _ else _) = _
  rw [if_neg (cross_ne_copyStart k), parserStep_cross_zero k hk]
  rfl

theorem oneStep_cross_zero_cons (k : Fin 73) (hk : k.1 < 72)
    (left : List (Tape CoreTape)) (y : Tape CoreTape)
    (right : List (Tape CoreTape)) :
    oneStep zero one work
      (.running (cross k) ⟨y :: left, .core zero, right⟩) =
      .running (cross (MStarParserMicrocode.next73 k hk))
        ⟨left, y, padDone :: right⟩ := by
  unfold oneStep
  change (if cross k = copyStart then _ else _) = _
  rw [if_neg (cross_ne_copyStart k), parserStep_cross_zero k hk]
  rfl

theorem oneStep_cross_wrong_core (k : Fin 73) (hk : k.1 < 72)
    (left right : List (Tape CoreTape)) (a : CoreTape) (ha : a ≠ zero) :
    oneStep zero one work (.running (cross k) ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if cross k = copyStart then _ else _) = _
  rw [if_neg (cross_ne_copyStart k), parserStep_cross_wrong_core k hk a ha]
  rfl

theorem oneStep_cross_noncore (k : Fin 73) (hk : k.1 < 72)
    (left right : List (Tape CoreTape)) (x : Tape CoreTape)
    (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running (cross k) ⟨left, x, right⟩) =
      .rejected := by
  unfold oneStep
  change (if cross k = copyStart then _ else _) = _
  rw [if_neg (cross_ne_copyStart k), parserStep_cross_noncore k hk x hx]
  simp [MStarParserMicrocode.reject, applyAction]

theorem cross_canAccept_forces_zero_and_left (k : Fin 73) (hk : k.1 < 72)
    (z : Zipper (Tape CoreTape))
    (hacc : CanAcceptResult (.running (cross k) z)) :
    z.focus = .core zero ∧ z.leftRev ≠ [] := by
  rcases z with ⟨left, focus, right⟩
  have hnext := (canAcceptResult_oneStep_iff _).2 hacc
  cases focus with
  | core a =>
      by_cases ha : a = zero
      · subst a
        refine ⟨rfl, ?_⟩
        intro hl
        change left = [] at hl
        subst left
        rw [oneStep_cross_zero_nil k hk] at hnext
        exact not_canAcceptResult_stuck hnext
      · rw [oneStep_cross_wrong_core k hk _ _ _ ha] at hnext
        exact (not_canAcceptResult_rejected hnext).elim
  | hash =>
      rw [oneStep_cross_noncore k hk _ _ .hash (by simp)] at hnext
      exact (not_canAcceptResult_rejected hnext).elim
  | markL =>
      rw [oneStep_cross_noncore k hk _ _ .markL (by simp)] at hnext
      exact (not_canAcceptResult_rejected hnext).elim
  | markR =>
      rw [oneStep_cross_noncore k hk _ _ .markR (by simp)] at hnext
      exact (not_canAcceptResult_rejected hnext).elim
  | scratch i =>
      rw [oneStep_cross_noncore k hk _ _ (.scratch i) (by simp)] at hnext
      exact (not_canAcceptResult_rejected hnext).elim

theorem cross_canAccept_forces_zero_prefix (k : Fin 73) (n : ℕ)
    (hbound : k.1 + n ≤ 72)
    (z : Zipper (Tape CoreTape))
    (hacc : CanAcceptResult (.running (cross k) z)) :
    (z.focus :: z.leftRev).take n =
      List.replicate n (Tape.core zero) := by
  induction n generalizing k z with
  | zero => rfl
  | succ n ih =>
      have hk : k.1 < 72 := by omega
      rcases cross_canAccept_forces_zero_and_left k hk z hacc with
        ⟨hzero, hleft⟩
      rcases z with ⟨left, focus, right⟩
      change focus = .core zero at hzero
      subst focus
      cases hleftList : left with
      | nil => exact (hleft hleftList).elim
      | cons y ys =>
          subst left
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          rw [oneStep_cross_zero_cons k hk] at hnext
          have hbound' : (MStarParserMicrocode.next73 k hk).1 + n ≤ 72 := by
            simp [MStarParserMicrocode.next73]
            omega
          have htail := ih (MStarParserMicrocode.next73 k hk) hbound'
            ⟨ys, y, padDone :: right⟩ hnext
          simpa [List.take, List.replicate_succ] using
            congrArg (fun xs => Tape.core zero :: xs) htail

theorem cross_canAccept_forces_room (k : Fin 73) (n : ℕ)
    (hbound : k.1 + n ≤ 72)
    (z : Zipper (Tape CoreTape))
    (hacc : CanAcceptResult (.running (cross k) z)) :
    n < (z.focus :: z.leftRev).length := by
  induction n generalizing k z with
  | zero => simp
  | succ n ih =>
      have hk : k.1 < 72 := by omega
      rcases cross_canAccept_forces_zero_and_left k hk z hacc with
        ⟨hzero, hleft⟩
      rcases z with ⟨left, focus, right⟩
      change focus = .core zero at hzero
      subst focus
      cases hleftList : left with
      | nil => exact (hleft hleftList).elim
      | cons y ys =>
          subst left
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          rw [oneStep_cross_zero_cons k hk] at hnext
          have hbound' : (MStarParserMicrocode.next73 k hk).1 + n ≤ 72 := by
            simp [MStarParserMicrocode.next73]
            omega
          have htail := ih (MStarParserMicrocode.next73 k hk) hbound'
            ⟨ys, y, padDone :: right⟩ hnext
          have htail' : n < (y :: ys).length := by simpa using htail
          simp only [List.length_cons] at htail' ⊢
          omega

theorem oneStep_seekUnmarked_endpoint
    (left right : List (Tape CoreTape)) :
    oneStep zero one work
      (.running seekUnmarkedPad ⟨left, endpointMark, right⟩) =
      .rejected := by
  rfl

/-- Every accepted length marker spends a fresh block of exactly 72 candidate
padding zeros.  This lemma proves the lower-bound half; the later separator
recheck supplies the matching upper bound. -/
theorem scanLen_zero_canAccept_forces_padding
    (padding : ℕ) (right : List (Tape CoreTape))
    (hacc : CanAcceptResult
      (.running scanLen
        ⟨sepPad :: List.replicate padding (Tape.core zero) ++ fixedPaddingTail,
          .core zero, right⟩)) :
    72 ≤ padding := by
  let low : List (Tape CoreTape) :=
    List.replicate padding (Tape.core zero) ++ fixedPaddingTail
  have hlow_ne : low ≠ [] := by
    simp [low, fixedPaddingTail]
  cases hlow : low with
  | nil => exact (hlow_ne hlow).elim
  | cons y ys =>
      have h₁ := (canAcceptResult_oneStep_iff _).2 hacc
      have hs₁ : oneStep zero one work
          (.running scanLen ⟨sepPad :: low, .core zero, right⟩) =
          .running seekSepPad ⟨low, sepPad, lenDone :: right⟩ :=
        MStarConcreteAlphabet.oneStep_scanLen_zero low sepPad right
      rw [show low = y :: ys by exact hlow] at hs₁
      have hstart :
          (.running scanLen
            ⟨sepPad :: List.replicate padding (Tape.core zero) ++ fixedPaddingTail,
              .core zero, right⟩ : Result CoreTape) =
          .running scanLen ⟨sepPad :: low, .core zero, right⟩ := by
        simp [low, List.append_assoc]
      rw [hstart, show low = y :: ys by exact hlow, hs₁] at h₁
      have h₂ := (canAcceptResult_oneStep_iff _).2 h₁
      rw [MStarConcreteAlphabet.oneStep_seekSepPad_separator] at h₂
      cases padding with
      | zero =>
          have hy : y = padDone ∧
              ys = List.replicate 70 padDone ++ [endpointMark] := by
            simpa [low, fixedPaddingTail, List.replicate_succ,
              List.append_assoc] using hlow.symm
          rcases hy with ⟨rfl, rfl⟩
          change CanAcceptResult
            (.running seekUnmarkedPad
              (beforeLeftRepeat 71 padDone [] endpointMark
                (sepPad :: lenDone :: right))) at h₂
          have hafter :=
            (canAcceptResult_run_iff 71
              (.running seekUnmarkedPad
                (beforeLeftRepeat 71 padDone [] endpointMark
                  (sepPad :: lenDone :: right)))).2 h₂
          rw [MStarConcreteAlphabet.run_seekUnmarked_padDone] at hafter
          change CanAcceptResult
            (.running seekUnmarkedPad
              ⟨[], endpointMark,
                List.replicate 71 padDone ++ sepPad :: lenDone :: right⟩) at hafter
          have hreject := (canAcceptResult_oneStep_iff _).2 hafter
          rw [oneStep_seekUnmarked_endpoint] at hreject
          exact (not_canAcceptResult_rejected hreject).elim
      | succ q =>
          have hy : y = Tape.core zero ∧
              ys = List.replicate q (Tape.core zero) ++ fixedPaddingTail := by
            simpa [low, List.replicate_succ, List.append_assoc] using hlow.symm
          rcases hy with ⟨rfl, rfl⟩
          let remaining : List (Tape CoreTape) :=
            List.replicate q (Tape.core zero) ++ fixedPaddingTail
          have hremaining_ne : remaining ≠ [] := by
            simp [remaining, fixedPaddingTail]
          cases hremaining : remaining with
          | nil => exact (hremaining_ne hremaining).elim
          | cons z zs =>
              have hcross := (canAcceptResult_oneStep_iff _).2 h₂
              have hstep : oneStep zero one work
                  (.running seekUnmarkedPad
                    ⟨remaining, .core zero, sepPad :: lenDone :: right⟩) =
                  .running (cross ⟨1, by decide⟩)
                    ⟨zs, z, padDone :: sepPad :: lenDone :: right⟩ := by
                rw [hremaining]
                exact MStarConcreteAlphabet.oneStep_seekUnmarked_zero
                  zs z (sepPad :: lenDone :: right)
              rw [show List.replicate q (Tape.core zero) ++ fixedPaddingTail =
                  remaining by rfl, hstep] at hcross
              have hprefix := cross_canAccept_forces_zero_prefix
                (⟨1, by decide⟩ : Fin 73) 71 (by decide)
                ⟨zs, z, padDone :: sepPad :: lenDone :: right⟩ hcross
              have hcountLe :=
                (List.take_sublist 71 (z :: zs)).count_le (Tape.core zero)
              have hcountTake :
                  ((z :: zs).take 71).count (Tape.core zero) = 71 := by
                rw [hprefix]
                simp
              have hcountAll :
                (z :: zs).count (Tape.core zero) = q := by
                rw [← hremaining]
                simp [remaining, fixedPaddingTail, padDone, endpointMark]
              rw [hcountTake, hcountAll] at hcountLe
              omega

def lengthState (paid padding : ℕ) (focus : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running scanLen
    ⟨List.replicate paid lenDone ++ sepPad ::
        (List.replicate (72 * paid) padDone ++
          List.replicate padding (Tape.core zero) ++ fixedPaddingTail),
      focus, right⟩

def unmarkedStart (padding : ℕ) (right : List (Tape CoreTape)) :
    Result CoreTape :=
  match List.replicate padding (Tape.core zero) ++ fixedPaddingTail with
  | [] => .stuck
  | y :: ys => .running seekUnmarkedPad ⟨ys, y, right⟩

theorem unmarkedStart_canAccept_forces_padding (padding : ℕ)
    (right : List (Tape CoreTape))
    (hacc : CanAcceptResult (unmarkedStart padding right)) :
    72 ≤ padding := by
  cases padding with
  | zero =>
      change CanAcceptResult
        (.running seekUnmarkedPad
          (beforeLeftRepeat 71 padDone [] endpointMark right)) at hacc
      have hafter :=
        (canAcceptResult_run_iff 71
          (.running seekUnmarkedPad
            (beforeLeftRepeat 71 padDone [] endpointMark right))).2 hacc
      rw [MStarConcreteAlphabet.run_seekUnmarked_padDone] at hafter
      change CanAcceptResult
        (.running seekUnmarkedPad
          ⟨[], endpointMark, List.replicate 71 padDone ++ right⟩) at hafter
      have hreject := (canAcceptResult_oneStep_iff _).2 hafter
      rw [oneStep_seekUnmarked_endpoint] at hreject
      exact (not_canAcceptResult_rejected hreject).elim
  | succ q =>
      change CanAcceptResult
        (.running seekUnmarkedPad
          ⟨List.replicate q (Tape.core zero) ++ fixedPaddingTail,
            .core zero, right⟩) at hacc
      let remaining : List (Tape CoreTape) :=
        List.replicate q (Tape.core zero) ++ fixedPaddingTail
      have hremaining_ne : remaining ≠ [] := by
        simp [remaining, fixedPaddingTail]
      cases hremaining : remaining with
      | nil => exact (hremaining_ne hremaining).elim
      | cons z zs =>
          have hcross := (canAcceptResult_oneStep_iff _).2 hacc
          have hstep : oneStep zero one work
              (.running seekUnmarkedPad ⟨remaining, .core zero, right⟩) =
              .running (cross ⟨1, by decide⟩) ⟨zs, z, padDone :: right⟩ := by
            rw [hremaining]
            exact MStarConcreteAlphabet.oneStep_seekUnmarked_zero zs z right
          rw [show List.replicate q (Tape.core zero) ++ fixedPaddingTail =
              remaining by rfl, hstep] at hcross
          have hprefix := cross_canAccept_forces_zero_prefix
            (⟨1, by decide⟩ : Fin 73) 71 (by decide)
            ⟨zs, z, padDone :: right⟩ hcross
          have hcountLe :=
            (List.take_sublist 71 (z :: zs)).count_le (Tape.core zero)
          have hcountTake :
              ((z :: zs).take 71).count (Tape.core zero) = 71 := by
            rw [hprefix]
            simp
          have hcountAll : (z :: zs).count (Tape.core zero) = q := by
            rw [← hremaining]
            simp [remaining, fixedPaddingTail, padDone, endpointMark]
          rw [hcountTake, hcountAll] at hcountLe
          omega

theorem reaches_unmarkedStart (paid padding : ℕ)
    (right : List (Tape CoreTape)) :
    Reaches zero one work
      (lengthState paid padding (.core zero) right)
      (unmarkedStart padding
        (List.replicate (72 * paid) padDone ++ sepPad ::
          List.replicate (paid + 1) lenDone ++ right)) := by
  let low : List (Tape CoreTape) :=
    List.replicate padding (Tape.core zero) ++ fixedPaddingTail
  have hlow_ne : low ≠ [] := by simp [low, fixedPaddingTail]
  cases hlow : low with
  | nil => exact (hlow_ne hlow).elim
  | cons y ys =>
      let padBelow : List (Tape CoreTape) :=
        List.replicate (72 * paid) padDone ++ low
      let z₁ : Result CoreTape :=
        .running seekSepPad
          (beforeLeftRepeat paid lenDone padBelow sepPad (lenDone :: right))
      let z₂ : Result CoreTape :=
        .running seekSepPad
          (afterLeftRepeat paid lenDone padBelow sepPad (lenDone :: right))
      have h₀₁ : Reaches zero one work
          (lengthState paid padding (.core zero) right) z₁ := by
        apply reaches_of_oneStep
        cases paid <;>
          simp [lengthState, z₁, padBelow, low, beforeLeftRepeat,
            MStarConcreteAlphabet.oneStep_scanLen_zero,
            List.replicate_succ, List.append_assoc]
      have h₁₂ : Reaches zero one work z₁ z₂ :=
        ⟨paid, MStarConcreteAlphabet.run_seekSepPad_lenDone paid
          padBelow sepPad (lenDone :: right)⟩
      let lenRight : List (Tape CoreTape) :=
        List.replicate (paid + 1) lenDone ++ right
      let z₃ : Result CoreTape :=
        .running seekUnmarkedPad
          (beforeLeftRepeat (72 * paid) padDone ys y (sepPad :: lenRight))
      let z₄ : Result CoreTape :=
        .running seekUnmarkedPad
          (afterLeftRepeat (72 * paid) padDone ys y (sepPad :: lenRight))
      have h₂₃ : Reaches zero one work z₂ z₃ := by
        apply reaches_of_oneStep
        have hright : List.replicate paid lenDone ++ lenDone :: right =
            lenRight := by
          simp [lenRight, List.replicate_succ', List.append_assoc]
        rw [show z₂ = .running seekSepPad
            ⟨List.replicate (72 * paid) padDone ++ y :: ys,
              sepPad, lenRight⟩ by
          simp only [z₂, afterLeftRepeat, padBelow]
          rw [show low = y :: ys by exact hlow, hright]]
        exact MStarConcreteAlphabet.separator_enters_left_repeat
          (72 * paid) ys y lenRight
      have h₃₄ : Reaches zero one work z₃ z₄ :=
        ⟨72 * paid, MStarConcreteAlphabet.run_seekUnmarked_padDone
          (72 * paid) ys y (sepPad :: lenRight)⟩
      have h₄f : z₄ = unmarkedStart padding
          (List.replicate (72 * paid) padDone ++ sepPad ::
            List.replicate (paid + 1) lenDone ++ right) := by
        unfold unmarkedStart
        rw [show List.replicate padding (Tape.core zero) ++ fixedPaddingTail =
          low by rfl, hlow]
        simp [z₄, afterLeftRepeat, lenRight, List.append_assoc]
      rw [h₄f] at h₃₄
      exact reaches_trans zero one work
        (reaches_trans zero one work h₀₁ h₁₂)
        (reaches_trans zero one work h₂₃ h₃₄)

theorem lengthState_zero_canAccept_forces_padding (paid padding : ℕ)
    (right : List (Tape CoreTape))
    (hacc : CanAcceptResult (lengthState paid padding (.core zero) right)) :
    72 ≤ padding := by
  have hunmarked := canAcceptResult_reaches_forward
    (reaches_unmarkedStart paid padding right) hacc
  exact unmarkedStart_canAccept_forces_padding padding
    (List.replicate (72 * paid) padDone ++ sepPad ::
      List.replicate (paid + 1) lenDone ++ right) hunmarked

@[simp] theorem returnLen_ne_copyStart : returnLen ≠ copyStart := by
  native_decide

theorem parserStep_returnLen (x : Tape CoreTape) :
    MStarParserMicrocode.step (UState := Unit) zero one work returnLen x =
      if x = lenDone then
        some (MStarParserMicrocode.go x returnLen .right)
      else some (MStarParserMicrocode.go x scanLen .stay) := by
  rfl

theorem oneStep_returnLen_other (left right : List (Tape CoreTape))
    (x : Tape CoreTape) (hx : x ≠ lenDone) :
    oneStep zero one work (.running returnLen ⟨left, x, right⟩) =
      .running scanLen ⟨left, x, right⟩ := by
  unfold oneStep
  change (if returnLen = copyStart then _ else _) = _
  rw [if_neg returnLen_ne_copyStart, parserStep_returnLen]
  simp [hx, MStarParserMicrocode.go, applyAction]

def generalFirstUnmarked (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running seekUnmarkedPad
    ⟨List.replicate (71 + extra) (Tape.core zero) ++ fixedPaddingTail,
      .core zero,
      List.replicate (72 * paid) padDone ++ sepPad ::
        List.replicate (paid + 1) lenDone ++ next :: right⟩

theorem reaches_generalFirstUnmarked (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (lengthState paid (72 + extra) (.core zero) (next :: right))
      (generalFirstUnmarked paid extra next right) := by
  let padBelow : List (Tape CoreTape) :=
    List.replicate (72 * paid) padDone ++
      List.replicate (72 + extra) (.core zero) ++ fixedPaddingTail
  let rightRest : List (Tape CoreTape) := next :: right
  let z₁ : Result CoreTape :=
    .running seekSepPad
      (beforeLeftRepeat paid lenDone padBelow sepPad (lenDone :: rightRest))
  let z₂ : Result CoreTape :=
    .running seekSepPad
      (afterLeftRepeat paid lenDone padBelow sepPad (lenDone :: rightRest))
  have h₀₁ : Reaches zero one work
      (lengthState paid (72 + extra) (.core zero) (next :: right)) z₁ := by
    apply reaches_of_oneStep
    cases paid <;>
      simp [lengthState, z₁, padBelow, rightRest, beforeLeftRepeat,
        MStarConcreteAlphabet.oneStep_scanLen_zero,
        List.replicate_succ, List.append_assoc]
  have h₁₂ : Reaches zero one work z₁ z₂ :=
    ⟨paid, MStarConcreteAlphabet.run_seekSepPad_lenDone paid padBelow sepPad
      (lenDone :: rightRest)⟩
  let low : List (Tape CoreTape) :=
    List.replicate (71 + extra) (.core zero) ++ fixedPaddingTail
  let lenRight : List (Tape CoreTape) :=
    List.replicate (paid + 1) lenDone ++ rightRest
  let z₃ : Result CoreTape :=
    .running seekUnmarkedPad
      (beforeLeftRepeat (72 * paid) padDone low (.core zero)
        (sepPad :: lenRight))
  let z₄ : Result CoreTape :=
    .running seekUnmarkedPad
      (afterLeftRepeat (72 * paid) padDone low (.core zero)
        (sepPad :: lenRight))
  have h₂₃ : Reaches zero one work z₂ z₃ := by
    apply reaches_of_oneStep
    have hpad : padBelow =
        List.replicate (72 * paid) padDone ++ .core zero :: low := by
      simp only [padBelow, low]
      rw [List.append_assoc]
      have h72 : 72 + extra = (71 + extra) + 1 := by omega
      rw [h72, List.replicate_succ']
      apply congrArg (fun xs => List.replicate (72 * paid) padDone ++ xs)
      simpa only [List.append_assoc, List.singleton_append] using
        (MStarConcreteAlphabet.replicate_cons_rotate
          (71 + extra) (Tape.core zero) fixedPaddingTail)
    have hright : List.replicate paid lenDone ++ lenDone :: rightRest =
        lenRight := by
      simp [lenRight, List.replicate_succ', List.append_assoc]
    rw [show z₂ = .running seekSepPad
        ⟨List.replicate (72 * paid) padDone ++ .core zero :: low,
          sepPad, lenRight⟩ by
      simp only [z₂, afterLeftRepeat]
      rw [hpad, hright]]
    exact MStarConcreteAlphabet.separator_enters_left_repeat
      (72 * paid) low (.core zero) lenRight
  have h₃₄ : Reaches zero one work z₃ z₄ :=
    ⟨72 * paid, MStarConcreteAlphabet.run_seekUnmarked_padDone
      (72 * paid) low (.core zero) (sepPad :: lenRight)⟩
  have h₄f : z₄ = generalFirstUnmarked paid extra next right := by
    simp [z₄, generalFirstUnmarked, low, lenRight, rightRest,
      afterLeftRepeat, List.append_assoc]
  rw [h₄f] at h₃₄
  exact reaches_trans zero one work
    (reaches_trans zero one work h₀₁ h₁₂)
    (reaches_trans zero one work h₂₃ h₃₄)

def generalAfterCross (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  match List.replicate extra (Tape.core zero) ++ fixedPaddingTail with
  | [] => .stuck
  | lowHead :: lowTail =>
      .running returnSepPad
        ⟨lowTail, lowHead,
          List.replicate 72 padDone ++
            List.replicate (72 * paid) padDone ++ sepPad ::
              List.replicate (paid + 1) lenDone ++ next :: right⟩

theorem reaches_generalAfterCross (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (generalFirstUnmarked paid extra next right)
      (generalAfterCross paid extra next right) := by
  let lower : List (Tape CoreTape) :=
    List.replicate extra (Tape.core zero) ++ fixedPaddingTail
  have hlower_ne : lower ≠ [] := by
    simp [lower, fixedPaddingTail]
  cases hlower : lower with
  | nil => exact (hlower_ne hlower).elim
  | cons lowHead lowTail =>
      let oldRight : List (Tape CoreTape) :=
        List.replicate (72 * paid) padDone ++ sepPad ::
          List.replicate (paid + 1) lenDone ++ next :: right
      let zcross : Result CoreTape :=
        .running (cross ⟨1, by decide⟩)
          ⟨List.replicate 70 (.core zero) ++ lowHead :: lowTail,
            .core zero, padDone :: oldRight⟩
      have hfirst : Reaches zero one work
          (generalFirstUnmarked paid extra next right) zcross := by
        apply reaches_of_oneStep
        have hleft :
            List.replicate (71 + extra) (Tape.core zero) ++ fixedPaddingTail =
              Tape.core zero ::
                (List.replicate 70 (Tape.core zero) ++ lowHead :: lowTail) := by
          rw [List.replicate_add, List.append_assoc]
          rw [show List.replicate extra (Tape.core zero) ++ fixedPaddingTail =
            lower by rfl, hlower]
          simp [List.replicate_succ, List.append_assoc]
        unfold generalFirstUnmarked zcross oldRight
        rw [hleft]
        exact MStarConcreteAlphabet.oneStep_seekUnmarked_zero
          (List.replicate 70 (.core zero) ++ lowHead :: lowTail)
          (.core zero)
          (List.replicate (72 * paid) padDone ++ sepPad ::
            List.replicate (paid + 1) lenDone ++ next :: right)
      have hcross : Reaches zero one work zcross
          (generalAfterCross paid extra next right) := by
        refine ⟨72, ?_⟩
        unfold generalAfterCross
        rw [show List.replicate extra (Tape.core zero) ++ fixedPaddingTail =
          lower by rfl, hlower]
        simpa [zcross, oldRight,
          List.replicate_add, List.append_assoc] using
          (MStarConcreteAlphabet.run_cross_remaining_71
            lowTail lowHead (padDone :: oldRight))
      exact reaches_trans zero one work hfirst hcross

def generalReturnStarted (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running returnSepPad
    (beforeRightRepeat (72 * (paid + 1)) padDone
      (List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
      sepPad (List.replicate (paid + 1) lenDone ++ next :: right))

theorem reaches_generalReturnStarted (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (generalAfterCross paid extra next right)
      (generalReturnStarted paid extra next right) := by
  apply reaches_of_oneStep
  cases extra with
  | zero =>
      unfold generalAfterCross generalReturnStarted
      rw [show 72 * (paid + 1) = (72 * (paid + 1) - 1) + 1 by omega]
      rw [show 72 * (paid + 1) - 1 = 71 + 72 * paid by omega]
      simp [fixedPaddingTail,
        beforeRightRepeat, MStarConcreteAlphabet.oneStep_returnSepPad_done,
        List.replicate_add, List.replicate_succ, List.append_assoc]
  | succ extra =>
      unfold generalAfterCross generalReturnStarted
      rw [show 72 * (paid + 1) = (72 * (paid + 1) - 1) + 1 by omega]
      rw [show 72 * (paid + 1) - 1 = 71 + 72 * paid by omega]
      simp [fixedPaddingTail,
        beforeRightRepeat, MStarConcreteAlphabet.oneStep_returnSepPad_zero,
        List.replicate_add, List.replicate_succ, List.append_assoc]

def generalReturnAtSep (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running returnSepPad
    (afterRightRepeat (72 * (paid + 1)) padDone
      (List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
      sepPad (List.replicate (paid + 1) lenDone ++ next :: right))

theorem reaches_generalReturnAtSep (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (generalReturnStarted paid extra next right)
      (generalReturnAtSep paid extra next right) :=
  ⟨72 * (paid + 1),
    MStarConcreteAlphabet.run_returnSepPad_done (72 * (paid + 1))
      (List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
      sepPad (List.replicate (paid + 1) lenDone ++ next :: right)⟩

def generalReturnLenStarted (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running returnLen
    (beforeRightRepeat (paid + 1) lenDone
      (sepPad :: List.replicate (72 * (paid + 1)) padDone ++
        List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
      next right)

theorem reaches_generalReturnLenStarted (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (generalReturnAtSep paid extra next right)
      (generalReturnLenStarted paid extra next right) := by
  apply reaches_of_oneStep
  cases paid with
  | zero =>
      simp [generalReturnAtSep, generalReturnLenStarted, afterRightRepeat,
        beforeRightRepeat, MStarConcreteAlphabet.oneStep_returnSepPad_separator,
        List.replicate_succ, List.append_assoc]
  | succ paid =>
      simp [generalReturnAtSep, generalReturnLenStarted, afterRightRepeat,
        beforeRightRepeat, MStarConcreteAlphabet.oneStep_returnSepPad_separator,
        List.replicate_succ, List.append_assoc]

def generalReturnAtNext (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running returnLen
    (afterRightRepeat (paid + 1) lenDone
      (sepPad :: List.replicate (72 * (paid + 1)) padDone ++
        List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
      next right)

theorem reaches_generalReturnAtNext (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (generalReturnLenStarted paid extra next right)
      (generalReturnAtNext paid extra next right) :=
  ⟨paid + 1, MStarConcreteAlphabet.run_returnLen_done (paid + 1)
    (sepPad :: List.replicate (72 * (paid + 1)) padDone ++
      List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
    next right⟩

theorem reaches_length_zero_iteration (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape))
    (hnext : next ≠ lenDone) :
    Reaches zero one work
      (lengthState paid (72 + extra) (.core zero) (next :: right))
      (lengthState (paid + 1) extra next right) := by
  have h₀ := reaches_generalFirstUnmarked paid extra next right
  have h₁ := reaches_generalAfterCross paid extra next right
  have h₂ := reaches_generalReturnStarted paid extra next right
  have h₃ := reaches_generalReturnAtSep paid extra next right
  have h₄ := reaches_generalReturnLenStarted paid extra next right
  have h₅ := reaches_generalReturnAtNext paid extra next right
  have h₆ : Reaches zero one work
      (generalReturnAtNext paid extra next right)
      (lengthState (paid + 1) extra next right) := by
    apply reaches_of_oneStep
    simpa [generalReturnAtNext, lengthState, afterRightRepeat,
      List.append_assoc] using
      oneStep_returnLen_other
        (List.replicate (paid + 1) lenDone ++
          (sepPad ::
            (List.replicate (72 * (paid + 1)) padDone ++
              (List.replicate extra (Tape.core zero) ++ fixedPaddingTail))))
        right next hnext
  exact reaches_trans zero one work h₀
    (reaches_trans zero one work h₁
      (reaches_trans zero one work h₂
        (reaches_trans zero one work h₃
          (reaches_trans zero one work h₄
            (reaches_trans zero one work h₅ h₆)))))

@[simp] theorem scanLen_ne_copyStart : scanLen ≠ copyStart := by
  native_decide

theorem parserStep_scanLen_core (a : CoreTape) :
    MStarParserMicrocode.step (UState := Unit) zero one work scanLen (.core a) =
      if MStarParserMicrocode.coreEq a zero then
        some (MStarParserMicrocode.go lenDone seekSepPad .left)
      else if MStarParserMicrocode.coreEq a one then
        some (MStarParserMicrocode.go sepLen checkSeekSepPad .left)
      else some (MStarParserMicrocode.reject (.core a)) := by
  rfl

theorem parserStep_scanLen_noncore (x : Tape CoreTape)
    (hx : ∀ a, x ≠ .core a) :
    MStarParserMicrocode.step (UState := Unit) zero one work scanLen x =
      some (MStarParserMicrocode.reject x) := by
  cases x with
  | core a => exact (hx a rfl).elim
  | hash | markL | markR | scratch => rfl

theorem oneStep_scanLen_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape)
    (hz : a ≠ zero) (ho : a ≠ one) :
    oneStep zero one work (.running scanLen ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if scanLen = copyStart then _ else _) = _
  rw [if_neg scanLen_ne_copyStart, parserStep_scanLen_core]
  simp [MStarParserMicrocode.coreEq, hz, ho,
    MStarParserMicrocode.reject, applyAction]

theorem oneStep_scanLen_noncore
    (left right : List (Tape CoreTape)) (x : Tape CoreTape)
    (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running scanLen ⟨left, x, right⟩) =
      .rejected := by
  unfold oneStep
  change (if scanLen = copyStart then _ else _) = _
  rw [if_neg scanLen_ne_copyStart, parserStep_scanLen_noncore x hx]
  simp [MStarParserMicrocode.reject, applyAction]

theorem lengthState_canAccept_split (paid padding : ℕ)
    (focus : Tape CoreTape) (right : List (Tape CoreTape))
    (hlast : (focus :: right).getLast? = some (.core work))
    (hraw : ∀ t, t ∈ focus :: right → ∃ a, t = .core a)
    (hacc : CanAcceptResult (lengthState paid padding focus right)) :
    ∃ m y ys,
      focus :: right =
        List.replicate m (Tape.core zero) ++ Tape.core one :: y :: ys ∧
      72 * m ≤ padding ∧
      CanAcceptResult
        (lengthState (paid + m) (padding - 72 * m) (.core one) (y :: ys)) := by
  induction right generalizing paid padding focus with
  | nil =>
      cases focus with
      | core a =>
          by_cases hz : a = zero
          · subst a
            simp [MStarConcreteAlphabet.zero_ne_work] at hlast
          · by_cases ho : a = one
            · subst a
              simp [MStarConcreteAlphabet.one_ne_work] at hlast
            · have hnext := (canAcceptResult_oneStep_iff _).2 hacc
              unfold lengthState at hnext
              rw [oneStep_scanLen_wrong_core _ _ _ hz ho] at hnext
              exact (not_canAcceptResult_rejected hnext).elim
      | hash =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ .hash (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markL =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ .markL (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markR =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ .markR (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | scratch i =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ (.scratch i) (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim

  | cons next rest ih =>
      cases focus with
      | core a =>
          by_cases hz : a = zero
          · subst a
            have hpad : 72 ≤ padding := by
              exact lengthState_zero_canAccept_forces_padding paid padding
                (next :: rest) hacc
            obtain ⟨extra, hpadding⟩ := Nat.exists_eq_add_of_le hpad
            rcases hraw next (by simp) with ⟨nextCore, rfl⟩
            have hrawNext : ∀ t,
                t ∈ (Tape.core nextCore :: rest) → ∃ a, t = .core a := by
              intro t ht
              exact hraw t (by simp_all)
            have hnextLetter :
                (Tape.core nextCore : Tape CoreTape) ≠ lenDone := by
              simp [lenDone]
            have hreach := reaches_length_zero_iteration paid extra
              (.core nextCore) rest
              hnextLetter
            have haccStart : CanAcceptResult
                (lengthState paid (72 + extra) (.core zero)
                  (.core nextCore :: rest)) := by
              simpa [hpadding] using hacc
            have haccNext := canAcceptResult_reaches_forward hreach haccStart
            have hlastNext : (Tape.core nextCore :: rest).getLast? =
                some (.core work) := by
              simpa using hlast
            rcases ih (paid + 1) extra (.core nextCore) hlastNext
              hrawNext haccNext with
              ⟨m, y, ys, hshape, hbound, hfinal⟩
            refine ⟨m + 1, y, ys, ?_, ?_, ?_⟩
            · simp [hshape, List.replicate_succ, List.append_assoc]
            · omega
            · have hpaid : paid + (m + 1) = paid + 1 + m := by omega
              have hmul : 72 * (m + 1) = 72 * m + 72 := by ring
              have hrem : padding - 72 * (m + 1) = extra - 72 * m := by
                rw [hpadding, hmul]
                omega
              rw [hpaid, hrem]
              exact hfinal
          · by_cases ho : a = one
            · subst a
              exact ⟨0, next, rest, rfl, by simp,
                by simpa [lengthState] using hacc⟩
            · have hnext := (canAcceptResult_oneStep_iff _).2 hacc
              unfold lengthState at hnext
              rw [oneStep_scanLen_wrong_core _ _ _ hz ho] at hnext
              exact (not_canAcceptResult_rejected hnext).elim
      | hash =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ .hash (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markL =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ .markL (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markR =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ .markR (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | scratch i =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hacc
          unfold lengthState at hnext
          rw [oneStep_scanLen_noncore _ _ (.scratch i) (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim

def checkPadStart (remaining : ℕ) (right : List (Tape CoreTape)) :
    Result CoreTape :=
  match List.replicate remaining (Tape.core zero) ++ fixedPaddingTail with
  | [] => .stuck
  | y :: ys => .running checkPad ⟨ys, y, right⟩

theorem oneStep_checkPad_coreZero (left right : List (Tape CoreTape)) :
    oneStep zero one work
      (.running checkPad ⟨left, .core zero, right⟩) = .rejected := by
  rfl

theorem checkPadStart_canAccept_forces_zero (remaining : ℕ)
    (right : List (Tape CoreTape))
    (hacc : CanAcceptResult (checkPadStart remaining right)) :
    remaining = 0 := by
  cases remaining with
  | zero => rfl
  | succ remaining =>
      change CanAcceptResult
        (.running checkPad
          ⟨List.replicate remaining (Tape.core zero) ++ fixedPaddingTail,
            .core zero, right⟩) at hacc
      have hnext := (canAcceptResult_oneStep_iff _).2 hacc
      rw [oneStep_checkPad_coreZero] at hnext
      exact (not_canAcceptResult_rejected hnext).elim

theorem checkSeparator_enters_left_repeat (n : ℕ)
    (left : List (Tape CoreTape)) (y : Tape CoreTape)
    (right : List (Tape CoreTape)) :
    oneStep zero one work
      (.running checkSeekSepPad
        ⟨List.replicate n padDone ++ y :: left, sepPad, right⟩) =
      .running checkPad
        (beforeLeftRepeat n padDone left y (sepPad :: right)) := by
  cases n <;>
    simp [beforeLeftRepeat, MStarConcreteAlphabet.oneStep_checkSeek_sepPad,
      List.replicate_succ, List.append_assoc]

theorem reaches_checkPadStart (paid remaining : ℕ)
    (right : List (Tape CoreTape)) :
    Reaches zero one work
      (lengthState paid remaining (.core one) right)
      (checkPadStart remaining
        (List.replicate (72 * paid) padDone ++ sepPad ::
          List.replicate paid lenDone ++ sepLen :: right)) := by
  let low : List (Tape CoreTape) :=
    List.replicate remaining (Tape.core zero) ++ fixedPaddingTail
  have hlow_ne : low ≠ [] := by simp [low, fixedPaddingTail]
  cases hlow : low with
  | nil => exact (hlow_ne hlow).elim
  | cons y ys =>
      let padBelow : List (Tape CoreTape) :=
        List.replicate (72 * paid) padDone ++ low
      let z₁ : Result CoreTape :=
        .running checkSeekSepPad
          (beforeLeftRepeat paid lenDone padBelow sepPad (sepLen :: right))
      let z₂ : Result CoreTape :=
        .running checkSeekSepPad
          (afterLeftRepeat paid lenDone padBelow sepPad (sepLen :: right))
      have h₀₁ : Reaches zero one work
          (lengthState paid remaining (.core one) right) z₁ := by
        apply reaches_of_oneStep
        cases paid <;>
          simp [lengthState, z₁, padBelow, low, beforeLeftRepeat,
            MStarConcreteAlphabet.oneStep_scanLen_separator,
            List.replicate_succ, List.append_assoc]
      have h₁₂ : Reaches zero one work z₁ z₂ :=
        ⟨paid, MStarConcreteAlphabet.run_checkSeek_lenDone paid
          padBelow sepPad (sepLen :: right)⟩
      let lenRight : List (Tape CoreTape) :=
        List.replicate paid lenDone ++ sepLen :: right
      let z₃ : Result CoreTape :=
        .running checkPad
          (beforeLeftRepeat (72 * paid) padDone ys y (sepPad :: lenRight))
      let z₄ : Result CoreTape :=
        .running checkPad
          (afterLeftRepeat (72 * paid) padDone ys y (sepPad :: lenRight))
      have h₂₃ : Reaches zero one work z₂ z₃ := by
        apply reaches_of_oneStep
        rw [show z₂ = .running checkSeekSepPad
            ⟨List.replicate (72 * paid) padDone ++ y :: ys,
              sepPad, lenRight⟩ by
          simp only [z₂, afterLeftRepeat, padBelow]
          rw [show low = y :: ys by exact hlow]]
        exact checkSeparator_enters_left_repeat (72 * paid) ys y lenRight
      have h₃₄ : Reaches zero one work z₃ z₄ :=
        ⟨72 * paid, MStarConcreteAlphabet.run_checkPad_done
          (72 * paid) ys y (sepPad :: lenRight)⟩
      have h₄f : z₄ = checkPadStart remaining
          (List.replicate (72 * paid) padDone ++ sepPad ::
            List.replicate paid lenDone ++ sepLen :: right) := by
        unfold checkPadStart
        rw [show List.replicate remaining (Tape.core zero) ++ fixedPaddingTail =
          low by rfl, hlow]
        simp [z₄, afterLeftRepeat, lenRight, List.append_assoc]
      rw [h₄f] at h₃₄
      exact reaches_trans zero one work
        (reaches_trans zero one work h₀₁ h₁₂)
        (reaches_trans zero one work h₂₃ h₃₄)

theorem lengthState_one_canAccept_forces_no_padding
    (paid remaining : ℕ) (right : List (Tape CoreTape))
    (hacc : CanAcceptResult (lengthState paid remaining (.core one) right)) :
    remaining = 0 := by
  have hcheck := canAcceptResult_reaches_forward
    (reaches_checkPadStart paid remaining right) hacc
  exact checkPadStart_canAccept_forces_zero remaining
    (List.replicate (72 * paid) padDone ++ sepPad ::
      List.replicate paid lenDone ++ sepLen :: right) hcheck

theorem inputCells_all_core (w : ConcretePakSide.Word) (t : Tape CoreTape)
    (ht : t ∈ inputCells zero one work w) : ∃ a, t = .core a := by
  simp only [inputCells, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with ⟨b, -, rfl⟩ | rfl
  · cases b <;> simp [bitCell]
  · exact ⟨work, rfl⟩

theorem parserAccepts_after_length (w : ConcretePakSide.Word)
    (hacc : Accepts zero one work w) :
    ∃ m y ys,
      inputCells zero one work w =
        List.replicate 72 (Tape.core zero) ++
          List.replicate (72 * m) (Tape.core zero) ++ Tape.core one ::
            List.replicate m (Tape.core zero) ++ Tape.core one :: y :: ys ∧
      CanAcceptResult (lengthState m 0 (.core one) (y :: ys)) := by
  rcases parserAccepts_after_scanPad w hacc with
    ⟨padding, focus, right, hinput, hscan⟩
  have hlength : CanAcceptResult (lengthState 0 padding focus right) := by
    simpa [lengthState, List.append_assoc] using hscan
  have hlastInput : (inputCells zero one work w).getLast? =
      some (.core work) := by
    simp [inputCells]
  have hlast : (focus :: right).getLast? = some (.core work) := by
    let pre : List (Tape CoreTape) :=
      List.replicate 72 (.core zero) ++
        List.replicate padding (.core zero) ++ [.core one]
    have hform : inputCells zero one work w = pre ++ (focus :: right) := by
      rw [hinput]
      simp [pre, List.append_assoc]
    rw [hform, List.getLast?_append_of_ne_nil pre (by simp)] at hlastInput
    exact hlastInput
  have hraw : ∀ t, t ∈ focus :: right → ∃ a, t = .core a := by
    intro t ht
    apply inputCells_all_core w t
    rw [hinput]
    simp [ht]
  rcases lengthState_canAccept_split 0 padding focus right hlast hraw hlength with
    ⟨m, y, ys, hshape, hbound, hfinal⟩
  have hremaining := lengthState_one_canAccept_forces_no_padding
    m (padding - 72 * m) (y :: ys) (by simpa using hfinal)
  have hpadding : padding = 72 * m := by omega
  refine ⟨m, y, ys, ?_, ?_⟩
  · rw [hinput, hshape, hpadding]
    simp [List.append_assoc]
  · simpa [hpadding] using hfinal

def pairingRawStarted (m : ℕ) (cells : List (Tape CoreTape)) :
    Result CoreTape :=
  .running findLen
    (beforeLeftRepeat m lenDone
      (List.replicate (72 * m + 71) padDone ++ [endpointMark])
      sepPad (sepLen :: cells))

theorem scanLenSeparator_enters_left_repeat (n : ℕ)
    (left : List (Tape CoreTape)) (right : List (Tape CoreTape)) :
    oneStep zero one work
      (.running scanLen
        ⟨List.replicate n lenDone ++ sepPad :: left, .core one, right⟩) =
      .running checkSeekSepPad
        (beforeLeftRepeat n lenDone left sepPad (sepLen :: right)) := by
  cases n <;>
    simp [beforeLeftRepeat, MStarConcreteAlphabet.oneStep_scanLen_separator,
      List.replicate_succ, MStarConcreteAlphabet.replicate_cons_rotate,
      List.append_assoc]

theorem reaches_pairingRawStarted (m : ℕ) (cells : List (Tape CoreTape)) :
    Reaches zero one work
      (lengthState m 0 (.core one) cells)
      (pairingRawStarted m cells) := by
  let lowPad : List (Tape CoreTape) :=
    List.replicate (72 * m + 71) padDone ++ [endpointMark]
  let z₁ : Result CoreTape :=
    .running checkSeekSepPad
      (beforeLeftRepeat m lenDone lowPad sepPad (sepLen :: cells))
  have h₀₁ : Reaches zero one work
      (lengthState m 0 (.core one) cells) z₁ := by
    apply reaches_of_oneStep
    have hpad : List.replicate (72 * m) padDone ++ fixedPaddingTail =
        lowPad := by
      simpa [lowPad] using MStarConcreteAlphabet.paddingDoneTailMerge m
    rw [show lengthState m 0 (.core one) cells =
        .running scanLen
          ⟨List.replicate m lenDone ++ sepPad :: lowPad,
            .core one, cells⟩ by
      simp [lengthState, hpad, List.append_assoc]]
    exact scanLenSeparator_enters_left_repeat m lowPad cells
  let z₂ : Result CoreTape :=
    .running checkSeekSepPad
      (afterLeftRepeat m lenDone lowPad sepPad (sepLen :: cells))
  have h₁₂ : Reaches zero one work z₁ z₂ :=
    ⟨m, MStarConcreteAlphabet.run_checkSeek_lenDone m lowPad sepPad
      (sepLen :: cells)⟩
  let nPad := 72 * m + 71
  let lenRight : List (Tape CoreTape) :=
    List.replicate m lenDone ++ sepLen :: cells
  let z₃ : Result CoreTape :=
    .running checkPad
      (beforeLeftRepeat nPad padDone [] endpointMark (sepPad :: lenRight))
  have h₂₃ : Reaches zero one work z₂ z₃ := by
    apply reaches_of_oneStep
    rw [show z₂ = .running checkSeekSepPad
        ⟨List.replicate nPad padDone ++ [endpointMark], sepPad, lenRight⟩ by
      simp [z₂, afterLeftRepeat, lowPad, lenRight, nPad,
        List.append_assoc]]
    exact checkSeparator_enters_left_repeat nPad [] endpointMark lenRight
  let z₄ : Result CoreTape :=
    .running checkPad
      (afterLeftRepeat nPad padDone [] endpointMark (sepPad :: lenRight))
  have h₃₄ : Reaches zero one work z₃ z₄ :=
    ⟨nPad, MStarConcreteAlphabet.run_checkPad_done nPad [] endpointMark
      (sepPad :: lenRight)⟩
  let z₅ : Result CoreTape :=
    .running checkReturnSepPad
      (beforeRightRepeat nPad padDone [endpointMark] sepPad lenRight)
  have h₄₅ : Reaches zero one work z₄ z₅ := by
    apply reaches_of_oneStep
    have hn : nPad = (72 * m + 70) + 1 := by simp [nPad]
    simp [z₄, z₅, afterLeftRepeat, beforeRightRepeat, nPad, hn,
      MStarConcreteAlphabet.oneStep_checkPad_endpoint,
      List.replicate_succ, List.append_assoc]
  let z₆ : Result CoreTape :=
    .running checkReturnSepPad
      (afterRightRepeat nPad padDone [endpointMark] sepPad lenRight)
  have h₅₆ : Reaches zero one work z₅ z₆ :=
    ⟨nPad, MStarConcreteAlphabet.run_checkReturnPad_done nPad
      [endpointMark] sepPad lenRight⟩
  let z₇ : Result CoreTape :=
    .running checkReturnSepLen
      (beforeRightRepeat m lenDone (sepPad :: lowPad) sepLen cells)
  have h₆₇ : Reaches zero one work z₆ z₇ := by
    apply reaches_of_oneStep
    cases m <;>
      simp [z₆, z₇, afterRightRepeat, beforeRightRepeat,
        lowPad, lenRight, nPad,
        MStarConcreteAlphabet.oneStep_checkReturnPad_sep,
        List.replicate_succ, List.append_assoc]
  let z₈ : Result CoreTape :=
    .running checkReturnSepLen
      (afterRightRepeat m lenDone (sepPad :: lowPad) sepLen cells)
  have h₇₈ : Reaches zero one work z₇ z₈ :=
    ⟨m, MStarConcreteAlphabet.run_checkReturnLen_done m
      (sepPad :: lowPad) sepLen cells⟩
  have h₈f : Reaches zero one work z₈ (pairingRawStarted m cells) := by
    apply reaches_of_oneStep
    cases m <;>
      simp [z₈, pairingRawStarted, afterRightRepeat, beforeLeftRepeat,
        lowPad, MStarConcreteAlphabet.oneStep_checkReturnLen_sep,
        List.replicate_succ, List.append_assoc]
  exact reaches_trans zero one work h₀₁
    (reaches_trans zero one work h₁₂
      (reaches_trans zero one work h₂₃
        (reaches_trans zero one work h₃₄
          (reaches_trans zero one work h₄₅
            (reaches_trans zero one work h₅₆
              (reaches_trans zero one work h₆₇
                (reaches_trans zero one work h₇₈ h₈f)))))))

def rawPairPad (total : ℕ) : List (Tape CoreTape) :=
  List.replicate (72 * total + 71) padDone ++ [endpointMark]

def pairRawBefore (done : List Bool) (remaining : ℕ)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running findLen
    (beforeLeftRepeat done.length pairedLen
      (List.replicate remaining lenDone ++ sepPad ::
        rawPairPad (done.length + remaining + 1))
      lenDone (sepLen :: done.map MStarConcreteAlphabet.payloadMarker ++ cells))

def pairRawFindAtFresh (done : List Bool) (remaining : ℕ)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running findLen
    (afterLeftRepeat done.length pairedLen
      (List.replicate remaining lenDone ++ sepPad ::
        rawPairPad (done.length + remaining + 1))
      lenDone (sepLen :: done.map MStarConcreteAlphabet.payloadMarker ++ cells))

def pairRawFreshMarked (done : List Bool) (remaining : ℕ)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running seekSepLenForPayload
    (beforeRightRepeat done.length pairedLen
      (pairedLen :: List.replicate remaining lenDone ++ sepPad ::
        rawPairPad (done.length + remaining + 1))
      sepLen (done.map MStarConcreteAlphabet.payloadMarker ++ cells))

def pairRawAtSepLen (done : List Bool) (remaining : ℕ)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running seekSepLenForPayload
    (afterRightRepeat done.length pairedLen
      (pairedLen :: List.replicate remaining lenDone ++ sepPad ::
        rawPairPad (done.length + remaining + 1))
      sepLen (done.map MStarConcreteAlphabet.payloadMarker ++ cells))

def pairRawPayloadStarted (done : List Bool) (remaining : ℕ)
    (focus : Tape CoreTape) (right : List (Tape CoreTape)) : Result CoreTape :=
  .running seekPayload
    (beforeRightList MStarConcreteAlphabet.payloadMarker done
      (sepLen :: List.replicate (done.length + 1) pairedLen ++
        List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1))
      focus right)

def pairRawAtPayload (done : List Bool) (remaining : ℕ)
    (focus : Tape CoreTape) (right : List (Tape CoreTape)) : Result CoreTape :=
  .running seekPayload
    (afterRightList MStarConcreteAlphabet.payloadMarker done
      (sepLen :: List.replicate (done.length + 1) pairedLen ++
        List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1))
      focus right)

theorem reaches_pairRawAtPayload (done : List Bool) (remaining : ℕ)
    (focus : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawBefore done remaining (focus :: right))
      (pairRawAtPayload done remaining focus right) := by
  have h₀₁ : Reaches zero one work
      (pairRawBefore done remaining (focus :: right))
      (pairRawFindAtFresh done remaining (focus :: right)) :=
    ⟨done.length, MStarConcreteAlphabet.run_findLen_paired done.length
      (List.replicate remaining lenDone ++ sepPad ::
        rawPairPad (done.length + remaining + 1))
      lenDone
      (sepLen :: done.map MStarConcreteAlphabet.payloadMarker ++ focus :: right)⟩
  have h₁₂ : Reaches zero one work
      (pairRawFindAtFresh done remaining (focus :: right))
      (pairRawFreshMarked done remaining (focus :: right)) := by
    apply reaches_of_oneStep
    cases done <;>
      simp [pairRawFindAtFresh, pairRawFreshMarked,
        afterLeftRepeat, beforeRightRepeat,
        MStarConcreteAlphabet.oneStep_findLen_fresh,
        List.replicate_succ, List.append_assoc]
  have h₂₃ : Reaches zero one work
      (pairRawFreshMarked done remaining (focus :: right))
      (pairRawAtSepLen done remaining (focus :: right)) :=
    ⟨done.length, MStarConcreteAlphabet.run_seekSepLen_paired done.length
      (pairedLen :: List.replicate remaining lenDone ++ sepPad ::
        rawPairPad (done.length + remaining + 1))
      sepLen (done.map MStarConcreteAlphabet.payloadMarker ++ focus :: right)⟩
  have h₃₄ : Reaches zero one work
      (pairRawAtSepLen done remaining (focus :: right))
      (pairRawPayloadStarted done remaining focus right) := by
    apply reaches_of_oneStep
    cases done <;>
      simp [pairRawAtSepLen, pairRawPayloadStarted,
        afterRightRepeat, beforeRightList,
        MStarConcreteAlphabet.oneStep_seekSepLen_separator,
        MStarConcreteAlphabet.replicate_cons_rotate,
        List.replicate_succ, List.append_assoc]
  have h₄₅ : Reaches zero one work
      (pairRawPayloadStarted done remaining focus right)
      (pairRawAtPayload done remaining focus right) :=
    ⟨done.length, MStarConcreteAlphabet.run_seekPayload_marked done
      (sepLen :: List.replicate (done.length + 1) pairedLen ++
        List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1))
      focus right⟩
  exact reaches_trans zero one work h₀₁
    (reaches_trans zero one work h₁₂
      (reaches_trans zero one work h₂₃
        (reaches_trans zero one work h₃₄ h₄₅)))

@[simp] theorem seekPayload_ne_copyStart : seekPayload ≠ copyStart := by
  native_decide

theorem parserStep_seekPayload_core (a : CoreTape) :
    MStarParserMicrocode.step (UState := Unit) zero one work seekPayload (.core a) =
      if MStarParserMicrocode.coreEq a zero then
        some (MStarParserMicrocode.go MStarParserMicrocode.payloadZero
          returnSepLenAfterPayload .left)
      else if MStarParserMicrocode.coreEq a one then
        some (MStarParserMicrocode.go MStarParserMicrocode.payloadOne
          returnSepLenAfterPayload .left)
      else some (MStarParserMicrocode.reject (.core a)) := by
  rfl

theorem oneStep_seekPayload_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape)
    (hz : a ≠ zero) (ho : a ≠ one) :
    oneStep zero one work (.running seekPayload ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if seekPayload = copyStart then _ else _) = _
  rw [if_neg seekPayload_ne_copyStart, parserStep_seekPayload_core]
  simp [MStarParserMicrocode.coreEq, hz, ho,
    MStarParserMicrocode.reject, applyAction]

theorem pairRawAtPayload_canAccept_forces_bit
    (done : List Bool) (remaining : ℕ)
    (left right : List (Tape CoreTape)) (a : CoreTape)
    (hacc : CanAcceptResult
      (.running seekPayload ⟨left, .core a, right⟩)) :
    a = zero ∨ a = one := by
  by_contra h
  push Not at h
  have hnext := (canAcceptResult_oneStep_iff _).2 hacc
  rw [oneStep_seekPayload_wrong_core left right a h.1 h.2] at hnext
  exact not_canAcceptResult_rejected hnext

def pairRawReturnStarted (done : List Bool) (remaining : ℕ) (b : Bool)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running returnSepLenAfterPayload
    (beforeLeftList MStarConcreteAlphabet.payloadMarker done.reverse
      (List.replicate (done.length + 1) pairedLen ++
        List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1))
      sepLen (MStarConcreteAlphabet.payloadMarker b :: cells))

theorem reaches_pairRawReturnStarted (done : List Bool) (remaining : ℕ)
    (b : Bool) (cells : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawAtPayload done remaining
        (MStarParserExecution.bitCell zero one b) cells)
      (pairRawReturnStarted done remaining b cells) := by
  apply reaches_of_oneStep
  cases hrev : done.reverse with
  | nil =>
      simp [pairRawAtPayload, pairRawReturnStarted, afterRightList,
        beforeLeftList, hrev, MStarConcreteAlphabet.oneStep_seekPayload_bit]
  | cons c cs =>
      simp [pairRawAtPayload, pairRawReturnStarted, afterRightList,
        beforeLeftList, hrev, MStarConcreteAlphabet.oneStep_seekPayload_bit,
        List.append_assoc]

def pairRawReturnedAtSep (done : List Bool) (remaining : ℕ) (b : Bool)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running returnSepLenAfterPayload
    (afterLeftList MStarConcreteAlphabet.payloadMarker done.reverse
      (List.replicate (done.length + 1) pairedLen ++
        List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1))
      sepLen (MStarConcreteAlphabet.payloadMarker b :: cells))

theorem reaches_pairRawReturnedAtSep (done : List Bool) (remaining : ℕ)
    (b : Bool) (cells : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawReturnStarted done remaining b cells)
      (pairRawReturnedAtSep done remaining b cells) :=
  ⟨done.length, by
    simpa [pairRawReturnStarted, pairRawReturnedAtSep] using
      (MStarConcreteAlphabet.run_returnPayload_marked done.reverse
        (List.replicate (done.length + 1) pairedLen ++
          (List.replicate remaining lenDone ++ sepPad ::
            rawPairPad (done.length + remaining + 1)))
        sepLen (MStarConcreteAlphabet.payloadMarker b :: cells))⟩

def pairRawAfterSep (done : List Bool) (remaining : ℕ) (b : Bool)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  .running findLen
    ⟨List.replicate done.length pairedLen ++
        List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1),
      pairedLen,
      sepLen :: done.map MStarConcreteAlphabet.payloadMarker ++
        MStarConcreteAlphabet.payloadMarker b :: cells⟩

theorem reaches_pairRawAfterSep (done : List Bool) (remaining : ℕ)
    (b : Bool) (cells : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawReturnedAtSep done remaining b cells)
      (pairRawAfterSep done remaining b cells) := by
  apply reaches_of_oneStep
  unfold pairRawReturnedAtSep pairRawAfterSep
  simp only [afterLeftList, List.length_reverse, List.reverse_reverse]
  rw [show done.length + 1 = Nat.succ done.length by omega,
    List.replicate_succ]
  simpa only [List.cons_append, List.append_assoc] using
    (MStarConcreteAlphabet.oneStep_returnPayload_separator
      (List.replicate done.length pairedLen ++
        (List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1)))
      pairedLen
      (done.map MStarConcreteAlphabet.payloadMarker ++
        MStarConcreteAlphabet.payloadMarker b :: cells))

def pairRawFinished (bits : List Bool) (cells : List (Tape CoreTape)) :
    Result CoreTape :=
  .running findLen
    ⟨rawPairPad bits.length, sepPad,
      List.replicate bits.length pairedLen ++ sepLen ::
        bits.map MStarConcreteAlphabet.payloadMarker ++ cells⟩

def pairRawNextState (done : List Bool) (remaining : ℕ) (b : Bool)
    (cells : List (Tape CoreTape)) : Result CoreTape :=
  match remaining with
  | 0 => pairRawFinished (done ++ [b]) cells
  | r + 1 => pairRawBefore (done ++ [b]) r cells

theorem reaches_pairRawNext (done : List Bool) (remaining : ℕ) (b : Bool)
    (cells : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawAfterSep done remaining b cells)
      (pairRawNextState done remaining b cells) := by
  cases remaining with
  | zero =>
      unfold pairRawNextState
      refine ⟨done.length + 1, ?_⟩
      simpa [pairRawAfterSep, pairRawFinished, pairRawBefore,
        afterLeftRepeat, beforeLeftRepeat, rawPairPad,
        List.map_append, List.replicate_succ, List.append_assoc] using
        (MStarConcreteAlphabet.run_findLen_paired (done.length + 1)
          (rawPairPad (done.length + 1)) sepPad
          (sepLen :: (done ++ [b]).map MStarConcreteAlphabet.payloadMarker ++ cells))
  | succ remaining =>
      unfold pairRawNextState
      rw [show pairRawAfterSep done (remaining + 1) b cells =
          pairRawBefore (done ++ [b]) remaining cells by
        cases done <;>
          simp [pairRawAfterSep, pairRawBefore, beforeLeftRepeat,
            rawPairPad, List.map_append, List.replicate_succ,
            MStarConcreteAlphabet.replicate_cons_rotate,
            List.append_assoc] <;> omega]
      exact reaches_refl zero one work _

theorem reaches_pairRaw_iteration (done : List Bool) (remaining : ℕ)
    (b : Bool) (cells : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawBefore done remaining
        (MStarParserExecution.bitCell zero one b :: cells))
      (pairRawNextState done remaining b cells) := by
  exact reaches_trans zero one work
    (reaches_pairRawAtPayload done remaining
      (MStarParserExecution.bitCell zero one b) cells)
    (reaches_trans zero one work
      (reaches_pairRawReturnStarted done remaining b cells)
      (reaches_trans zero one work
        (reaches_pairRawReturnedAtSep done remaining b cells)
        (reaches_trans zero one work
          (reaches_pairRawAfterSep done remaining b cells)
          (reaches_pairRawNext done remaining b cells))))

theorem pairRaw_canAccept_step (done : List Bool) (remaining : ℕ)
    (cells : List (Tape CoreTape))
    (hlast : cells.getLast? = some (.core work))
    (hraw : ∀ t, t ∈ cells → ∃ a, t = .core a)
    (hacc : CanAcceptResult (pairRawBefore done remaining cells)) :
    ∃ b rest,
      cells = MStarParserExecution.bitCell zero one b :: rest ∧
      CanAcceptResult (pairRawNextState done remaining b rest) := by
  cases hcells : cells with
  | nil => simp [hcells] at hlast
  | cons focus rest =>
      rcases hraw focus (by simp [hcells]) with ⟨a, ha⟩
      subst focus
      have hat := canAcceptResult_reaches_forward
        (reaches_pairRawAtPayload done remaining (.core a) rest)
        (by simpa [hcells] using hacc)
      unfold pairRawAtPayload at hat
      have hab := pairRawAtPayload_canAccept_forces_bit done remaining
        _ rest a hat
      rcases hab with hzero | hone
      · subst a
        refine ⟨false, rest, ?_, ?_⟩
        · simpa [hcells, bitCell]
        · exact canAcceptResult_reaches_forward
            (reaches_pairRaw_iteration done remaining false rest)
            (by simpa [hcells, bitCell] using hacc)
      · subst a
        refine ⟨true, rest, ?_, ?_⟩
        · simpa [hcells, bitCell]
        · exact canAcceptResult_reaches_forward
            (reaches_pairRaw_iteration done remaining true rest)
            (by simpa [hcells, bitCell] using hacc)

theorem pairRaw_canAccept_fold (done : List Bool) (remaining : ℕ)
    (cells : List (Tape CoreTape))
    (hlast : cells.getLast? = some (.core work))
    (hraw : ∀ t, t ∈ cells → ∃ a, t = .core a)
    (hacc : CanAcceptResult (pairRawBefore done remaining cells)) :
    ∃ bits rest,
      bits.length = remaining + 1 ∧
      cells = bits.map (MStarParserExecution.bitCell zero one) ++ rest ∧
      CanAcceptResult (pairRawFinished (done ++ bits) rest) := by
  induction remaining generalizing done cells with
  | zero =>
      rcases pairRaw_canAccept_step done 0 cells hlast hraw hacc with
        ⟨b, rest, hcells, hfinal⟩
      exact ⟨[b], rest, by simp, by simpa [hcells],
        by simpa [pairRawNextState] using hfinal⟩
  | succ remaining ih =>
      rcases pairRaw_canAccept_step done (remaining + 1) cells hlast hraw hacc with
        ⟨b, rest, hcells, hnext⟩
      have hlastRest : rest.getLast? = some (.core work) := by
        rw [hcells] at hlast
        cases rest with
        | nil => cases b <;> simp [bitCell] at hlast
        | cons t ts => simpa using hlast
      have hrawRest : ∀ t, t ∈ rest → ∃ a, t = .core a := by
        intro t ht
        apply hraw t
        rw [hcells]
        simp [ht]
      rcases ih (done ++ [b]) rest hlastRest hrawRest hnext with
        ⟨bits, tail, hlen, hrest, hfinal⟩
      refine ⟨b :: bits, tail, ?_, ?_, ?_⟩
      · simp [hlen]
      · rw [hcells, hrest]
        simp [List.append_assoc]
      · simpa [List.append_assoc] using hfinal

theorem pairingRawStarted_zero_eq_finished (cells : List (Tape CoreTape)) :
    pairingRawStarted 0 cells = pairRawFinished [] cells := by
  rfl

theorem pairingRawStarted_succ_eq_before (remaining : ℕ)
    (cells : List (Tape CoreTape)) :
    pairingRawStarted (remaining + 1) cells = pairRawBefore [] remaining cells := by
  simp [pairingRawStarted, pairRawBefore, beforeLeftRepeat,
    rawPairPad, List.append_assoc]

theorem pairingRaw_canAccept_extract (m : ℕ)
    (cells : List (Tape CoreTape))
    (hlast : cells.getLast? = some (.core work))
    (hraw : ∀ t, t ∈ cells → ∃ a, t = .core a)
    (hacc : CanAcceptResult (pairingRawStarted m cells)) :
    ∃ bits rest,
      bits.length = m ∧
      cells = bits.map (MStarParserExecution.bitCell zero one) ++ rest ∧
      CanAcceptResult (pairRawFinished bits rest) := by
  cases m with
  | zero =>
      rw [pairingRawStarted_zero_eq_finished] at hacc
      exact ⟨[], cells, rfl, rfl, hacc⟩
  | succ remaining =>
      rw [pairingRawStarted_succ_eq_before] at hacc
      rcases pairRaw_canAccept_fold [] remaining cells hlast hraw hacc with
        ⟨bits, rest, hlen, hcells, hfinal⟩
      exact ⟨bits, rest, by omega, hcells, by simpa using hfinal⟩

def verifyRawStarted (bits : List Bool) (cells : List (Tape CoreTape)) :
    Result CoreTape :=
  .running verifySeekSepLen
    (beforeRightRepeat bits.length pairedLen
      (sepPad :: rawPairPad bits.length) sepLen
      (bits.map MStarConcreteAlphabet.payloadMarker ++ cells))

def verifyRawAtSepLen (bits : List Bool) (cells : List (Tape CoreTape)) :
    Result CoreTape :=
  .running verifySeekSepLen
    (afterRightRepeat bits.length pairedLen
      (sepPad :: rawPairPad bits.length) sepLen
      (bits.map MStarConcreteAlphabet.payloadMarker ++ cells))

def verifyRawPayloadStarted (bits : List Bool) (focus : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running verifyPayload
    (beforeRightList MStarConcreteAlphabet.payloadMarker bits
      (sepLen :: List.replicate bits.length pairedLen ++
        sepPad :: rawPairPad bits.length) focus right)

def verifyRawAtSuffix (bits : List Bool) (focus : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running verifyPayload
    (afterRightList MStarConcreteAlphabet.payloadMarker bits
      (sepLen :: List.replicate bits.length pairedLen ++
        sepPad :: rawPairPad bits.length) focus right)

theorem reaches_verifyRawAtSuffix (bits : List Bool)
    (focus : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (pairRawFinished bits (focus :: right))
      (verifyRawAtSuffix bits focus right) := by
  have h₀₁ : Reaches zero one work
      (pairRawFinished bits (focus :: right))
      (verifyRawStarted bits (focus :: right)) := by
    apply reaches_of_oneStep
    cases bits <;>
      simp [pairRawFinished, verifyRawStarted, beforeRightRepeat,
        MStarConcreteAlphabet.oneStep_findLen_finished,
        rawPairPad, List.replicate_succ, List.append_assoc]
  have h₁₂ : Reaches zero one work
      (verifyRawStarted bits (focus :: right))
      (verifyRawAtSepLen bits (focus :: right)) :=
    ⟨bits.length, MStarConcreteAlphabet.run_verifySeek_paired bits.length
      (sepPad :: rawPairPad bits.length) sepLen
      (bits.map MStarConcreteAlphabet.payloadMarker ++ focus :: right)⟩
  have h₂₃ : Reaches zero one work
      (verifyRawAtSepLen bits (focus :: right))
      (verifyRawPayloadStarted bits focus right) := by
    apply reaches_of_oneStep
    cases bits <;>
      simp [verifyRawAtSepLen, verifyRawPayloadStarted,
        afterRightRepeat, beforeRightList,
        MStarConcreteAlphabet.oneStep_verifySeek_separator,
        List.replicate_succ, List.append_assoc]
  have h₃₄ : Reaches zero one work
      (verifyRawPayloadStarted bits focus right)
      (verifyRawAtSuffix bits focus right) :=
    ⟨bits.length, MStarConcreteAlphabet.run_verifyPayload_marked bits
      (sepLen :: List.replicate bits.length pairedLen ++
        sepPad :: rawPairPad bits.length) focus right⟩
  exact reaches_trans zero one work h₀₁
    (reaches_trans zero one work h₁₂
      (reaches_trans zero one work h₂₃ h₃₄))

@[simp] theorem verifyPayload_ne_copyStart : verifyPayload ≠ copyStart := by
  native_decide

theorem parserStep_verifyPayload_core (a : CoreTape) :
    MStarParserMicrocode.step (UState := Unit) zero one work verifyPayload (.core a) =
      if MStarParserMicrocode.coreEq a one then
        some (MStarParserMicrocode.go endpointMark verifyHigh .right)
      else some (MStarParserMicrocode.reject (.core a)) := by
  rfl

theorem oneStep_verifyPayload_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape) (ha : a ≠ one) :
    oneStep zero one work (.running verifyPayload ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if verifyPayload = copyStart then _ else _) = _
  rw [if_neg verifyPayload_ne_copyStart, parserStep_verifyPayload_core]
  simp [MStarParserMicrocode.coreEq, ha,
    MStarParserMicrocode.reject, applyAction]

theorem oneStep_verifyPayload_one_nil (left : List (Tape CoreTape)) :
    oneStep zero one work (.running verifyPayload ⟨left, .core one, []⟩) =
      .stuck := by
  rfl

theorem oneStep_verifyPayload_one_cons (left : List (Tape CoreTape))
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    oneStep zero one work
      (.running verifyPayload ⟨left, .core one, next :: right⟩) =
      .running verifyHigh ⟨endpointMark :: left, next, right⟩ := by
  rfl

@[simp] theorem verifyHigh_ne_copyStart : verifyHigh ≠ copyStart := by
  native_decide

theorem parserStep_verifyHigh_core (a : CoreTape) :
    MStarParserMicrocode.step (UState := Unit) zero one work verifyHigh (.core a) =
      if MStarParserMicrocode.coreEq a work then
        some (MStarParserMicrocode.go (.core a) copyStart .stay)
      else some (MStarParserMicrocode.reject (.core a)) := by
  rfl

theorem oneStep_verifyHigh_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape) (ha : a ≠ work) :
    oneStep zero one work (.running verifyHigh ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if verifyHigh = copyStart then _ else _) = _
  rw [if_neg verifyHigh_ne_copyStart, parserStep_verifyHigh_core]
  simp [MStarParserMicrocode.coreEq, ha,
    MStarParserMicrocode.reject, applyAction]

theorem pairRawFinished_canAccept_forces_suffix (bits : List Bool)
    (cells : List (Tape CoreTape))
    (hlast : cells.getLast? = some (.core work))
    (hraw : ∀ t, t ∈ cells → ∃ a, t = .core a)
    (hacc : CanAcceptResult (pairRawFinished bits cells)) :
    ∃ tail, cells = [.core one, .core work] ++ tail := by
  cases hcells : cells with
  | nil => simp [hcells] at hlast
  | cons focus right =>
      rcases hraw focus (by simp [hcells]) with ⟨a, rfl⟩
      have hsuffix := canAcceptResult_reaches_forward
        (reaches_verifyRawAtSuffix bits (.core a) right)
        (by simpa [hcells] using hacc)
      unfold verifyRawAtSuffix at hsuffix
      simp only [afterRightList] at hsuffix
      by_cases ha : a = one
      · subst a
        cases hright : right with
        | nil =>
            subst right
            have hnext := (canAcceptResult_oneStep_iff _).2 hsuffix
            rw [oneStep_verifyPayload_one_nil] at hnext
            exact (not_canAcceptResult_stuck hnext).elim
        | cons next tail =>
            subst right
            have hhigh := (canAcceptResult_oneStep_iff _).2 hsuffix
            rw [oneStep_verifyPayload_one_cons] at hhigh
            rcases hraw next (by simp [hcells]) with ⟨a, rfl⟩
            by_cases hw : a = work
            · subst a
              exact ⟨tail, by simp [hcells]⟩
            · have hnext := (canAcceptResult_oneStep_iff _).2 hhigh
              rw [oneStep_verifyHigh_wrong_core _ _ _ hw] at hnext
              exact (not_canAcceptResult_rejected hnext).elim
      · have hnext := (canAcceptResult_oneStep_iff _).2 hsuffix
        rw [oneStep_verifyPayload_wrong_core _ _ _ ha] at hnext
        exact (not_canAcceptResult_rejected hnext).elim

theorem work_not_mem_bitCells (bits : List Bool) :
    (Tape.core work : Tape CoreTape) ∉
      bits.map (MStarParserExecution.bitCell zero one) := by
  intro h
  rcases List.mem_map.mp h with ⟨b, -, hb⟩
  cases b <;> simp [bitCell] at hb

theorem getLast?_ne_work_of_not_mem (cells : List (Tape CoreTape))
    (hnot : (Tape.core work : Tape CoreTape) ∉ cells) :
    cells.getLast? ≠ some (.core work) := by
  intro hlast
  have hopt : (Tape.core work : Tape CoreTape) ∈ cells.getLast? := by
    simp [hlast]
  rcases List.mem_getLast?_eq_getLast hopt with ⟨hne, heq⟩
  have hmem := List.getLast_mem hne
  rw [← heq] at hmem
  exact hnot hmem

theorem inputCells_count_work (w : ConcretePakSide.Word) :
    (inputCells zero one work w).count (Tape.core work) = 1 := by
  unfold inputCells
  rw [List.count_append]
  have hzero :
      (w.reverse.map (MStarParserExecution.bitCell zero one)).count
        (Tape.core work) = 0 :=
    List.count_eq_zero_of_not_mem (work_not_mem_bitCells w.reverse)
  rw [hzero]
  simp

theorem inputCells_work_tail_nil (w : ConcretePakSide.Word)
    (pre tail : List (Tape CoreTape))
    (hshape : inputCells zero one work w = pre ++ .core work :: tail) :
    tail = [] := by
  have hcount := inputCells_count_work w
  rw [hshape] at hcount
  have htailCount : tail.count (Tape.core work) = 0 := by
    simp only [List.count_append, List.count_cons] at hcount
    simp at hcount
    omega
  cases htail : tail with
  | nil => rfl
  | cons t ts =>
      have hlastInput : (inputCells zero one work w).getLast? =
          some (.core work) := by simp [inputCells]
      rw [hshape, List.getLast?_append_of_ne_nil pre (by simp)] at hlastInput
      rw [htail] at htailCount
      have hopt : (Tape.core work : Tape CoreTape) ∈ (t :: ts).getLast? := by
        simpa [htail] using hlastInput
      rcases List.mem_getLast?_eq_getLast hopt with ⟨hne, heq⟩
      have hmem := List.getLast_mem hne
      rw [← heq] at hmem
      have hpos := List.count_pos_iff.mpr hmem
      omega

theorem inputCells_injective :
    Function.Injective (inputCells zero one work) := by
  intro u v h
  unfold inputCells at h
  have hmap : u.reverse.map (MStarParserExecution.bitCell zero one) =
      v.reverse.map (MStarParserExecution.bitCell zero one) :=
    (List.append_left_injective [Tape.core work]) h
  have hreverse : u.reverse = v.reverse :=
    (List.map_injective_iff.mpr bitCell_injective) hmap
  exact List.reverse_injective hreverse

theorem parserAccepts_sound (w : ConcretePakSide.Word)
    (hacc : Accepts zero one work w) :
    ∃ x, ConcretePakSide.encodedWord x = w := by
  rcases parserAccepts_after_length w hacc with
    ⟨m, focus, right, hinput, hlength⟩
  let cells := focus :: right
  have hlastInput : (inputCells zero one work w).getLast? =
      some (.core work) := by simp [inputCells]
  have hlast : cells.getLast? = some (.core work) := by
    let pre : List (Tape CoreTape) :=
      List.replicate 72 (.core zero) ++
        List.replicate (72 * m) (.core zero) ++ .core one ::
          List.replicate m (.core zero) ++ [.core one]
    have hform : inputCells zero one work w = pre ++ cells := by
      rw [hinput]
      simp [pre, cells, List.append_assoc]
    rw [hform, List.getLast?_append_of_ne_nil pre (by simp [cells])] at hlastInput
    exact hlastInput
  have hraw : ∀ t, t ∈ cells → ∃ a, t = .core a := by
    intro t ht
    apply inputCells_all_core w t
    rw [hinput]
    simp [cells, ht]
  have hpair : CanAcceptResult (pairingRawStarted m cells) :=
    canAcceptResult_reaches_forward (reaches_pairingRawStarted m cells)
      (by simpa [cells] using hlength)
  rcases pairingRaw_canAccept_extract m cells hlast hraw hpair with
    ⟨bits, rest, hbitsLen, hcells, hfinished⟩
  have hrest_ne : rest ≠ [] := by
    intro hnil
    subst rest
    rw [hcells] at hlast
    have hlast' :
        (bits.map (MStarParserExecution.bitCell zero one)).getLast? =
          some (.core work) := by simpa using hlast
    exact (getLast?_ne_work_of_not_mem
      (bits.map (MStarParserExecution.bitCell zero one))
      (work_not_mem_bitCells bits)) hlast'
  have hlastRest : rest.getLast? = some (.core work) := by
    rw [hcells, List.getLast?_append_of_ne_nil
      (bits.map (MStarParserExecution.bitCell zero one)) hrest_ne] at hlast
    exact hlast
  have hrawRest : ∀ t, t ∈ rest → ∃ a, t = .core a := by
    intro t ht
    apply hraw t
    rw [hcells]
    simp [ht]
  rcases pairRawFinished_canAccept_forces_suffix bits rest hlastRest hrawRest
      hfinished with ⟨tail, hrest⟩
  have hfull : inputCells zero one work w =
      List.replicate 72 (.core zero) ++
        List.replicate (72 * m) (.core zero) ++ .core one ::
          List.replicate m (.core zero) ++ .core one ::
            bits.map (MStarParserExecution.bitCell zero one) ++
              [.core one, .core work] ++ tail := by
    rw [hinput, show focus :: right = cells by rfl, hcells, hrest]
    simp [List.append_assoc]
  let pre : List (Tape CoreTape) :=
    List.replicate 72 (.core zero) ++
      List.replicate (72 * m) (.core zero) ++ .core one ::
        List.replicate m (.core zero) ++ .core one ::
          bits.map (MStarParserExecution.bitCell zero one) ++ [.core one]
  have hdecomp : inputCells zero one work w = pre ++ .core work :: tail := by
    rw [hfull]
    simp [pre, List.append_assoc]
  have htail := inputCells_work_tail_nil w pre tail hdecomp
  subst tail
  refine ⟨bits.reverse, ?_⟩
  apply inputCells_injective
  rw [MStarParserExecution.inputCells_encodedWord]
  rw [hfull]
  have hpad : ConcretePakSide.paddingLength bits.reverse.length =
      72 + 72 * m := by
    simp [ConcretePakSide.paddingLength, hbitsLen]
    omega
  rw [hpad, List.replicate_add]
  simp [hbitsLen, List.append_assoc]

theorem parser_accepts_iff_decodeWord (w : ConcretePakSide.Word) :
    Accepts zero one work w ↔ ∃ x, ConcretePakSide.decodeWord w = some x := by
  constructor
  · intro hacc
    rcases parserAccepts_sound w hacc with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx]
    exact ConcretePakSide.decodeWord_encodedWord x
  · rintro ⟨x, hx⟩
    have hw := ConcretePakSide.decodeWord_sound hx
    rw [← hw]
    exact MStarConcreteAlphabet.parser_accepts_encodedWord x

end PakFixedPolyomino.MStarParserSoundness
