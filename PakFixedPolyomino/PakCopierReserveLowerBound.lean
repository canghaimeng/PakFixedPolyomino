import PakFixedPolyomino.PakCopierSlackExecution

/-! # Necessary copier reserve, one physical doubling round

Forward copier proofs package the exact work reserve into `roundStage`.  For
reflection we keep the number of old cells and the number of actually
available work cells independent.  A successful continuation must spend one
work cell per old cell; encountering the terminal marker earlier takes the
literal reject edge.
-/

namespace PakFixedPolyomino.PakCopierReserveLowerBound

open MStarCopierMicrocode MStarCopierExecution MStarOuterProgram

abbrev ConcreteTape := MStarCopierMicrocode.ConcreteTape
abbrev Zipper := MStarParserExecution.Zipper ConcreteTape
abbrev Result := MStarCopierExecution.Result

def CanFinish (r : Result) : Prop :=
  ∃ fuel out, run fuel r = .groupReady out

theorem canFinish_of_reaches {a b : Result}
    (hab : Reaches a b) (ha : CanFinish a) : CanFinish b := by
  rcases hab with ⟨p, hp⟩
  rcases ha with ⟨q, out, hq⟩
  rcases Nat.le_total p q with hpq | hqp
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [run_add, hp] at hq
    exact ⟨d, out, hq⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqp
    rw [run_add, hq, groupReady_absorbing] at hp
    have hb : b = .groupReady out := hp.symm
    subst b
    exact ⟨0, out, rfl⟩

theorem not_canFinish_rejected : ¬ CanFinish .rejected := by
  rintro ⟨fuel, out, h⟩
  rw [rejected_absorbing] at h
  cases h

theorem not_canFinish_stuck : ¬ CanFinish .stuck := by
  rintro ⟨fuel, out, h⟩
  rw [stuck_absorbing] at h
  cases h

/-- A round home with `available` actual work cells after the moving barrier.
Unlike `roundStage`, this definition does not assume that `available` equals
the number of unprocessed old cells. -/
def rawRoundStage (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) : Result :=
  match processed, remaining with
  | 0, 0 => .stuck
  | 0, u + 1 =>
      .running (.findOld r)
        ⟨.markL :: source, cellA,
          List.replicate u cellA ++ .markR ::
            List.replicate available (.core MStarConcreteAlphabet.work) ++
              rightEnd :: external⟩
  | k + 1, u =>
      .running (.findOld r)
        ⟨.markL :: source, cellB,
          List.replicate k cellB ++ List.replicate u cellA ++
            List.replicate (k + 1) cellB ++ .markR ::
              List.replicate available (.core MStarConcreteAlphabet.work) ++
                rightEnd :: external⟩

def rawAtOld (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) : Result :=
  .running (.findOld r)
    (afterRightRepeat processed cellB (.markL :: source) cellA
      (List.replicate remaining cellA ++ List.replicate processed cellB ++
        .markR :: List.replicate available
          (.core MStarConcreteAlphabet.work) ++ rightEnd :: external))

def rawSeekStarted (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) : Result :=
  .running (.seekBoundary r)
    (beforeRightList (seekCells processed remaining)
      (cellB :: List.replicate processed cellB ++ .markL :: source) .markR
      (List.replicate available (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external))

def rawAtBoundary (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) : Result :=
  .running (.seekBoundary r)
    (afterRightList (seekCells processed remaining)
      (cellB :: List.replicate processed cellB ++ .markL :: source) .markR
      (List.replicate available (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external))

theorem reaches_rawAtOld (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) :
    Reaches (rawRoundStage r processed (remaining + 1) available external source)
      (rawAtOld r processed remaining available external source) := by
  refine ⟨processed, ?_⟩
  have hrun := run_findOld_B r processed (.markL :: source) cellA
    (List.replicate remaining cellA ++ List.replicate processed cellB ++
      .markR :: List.replicate available (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external)
  cases processed with
  | zero => simpa [rawRoundStage, rawAtOld, beforeRightRepeat] using hrun
  | succ processed =>
      simpa [rawRoundStage, rawAtOld, beforeRightRepeat,
        List.replicate_succ, List.append_assoc] using hrun

theorem reaches_rawSeekStarted (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape) :
    Reaches (rawAtOld r processed remaining available external source)
      (rawSeekStarted r processed remaining available external source) := by
  apply reaches_of_oneStep
  cases processed <;> cases remaining <;>
    simp [rawAtOld, rawSeekStarted, seekCells, afterRightRepeat,
      beforeRightList, findOld_A_step, List.replicate_succ,
      List.append_assoc]

theorem reaches_rawAtBoundary (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape) :
    Reaches (rawSeekStarted r processed remaining available external source)
      (rawAtBoundary r processed remaining available external source) := by
  refine ⟨(seekCells processed remaining).length, ?_⟩
  apply run_right_list_of (.seekBoundary r) (seekCells processed remaining)
  intro x hx left y right
  have hcell : x = cellA ∨ x = cellB := by
    simp [seekCells] at hx
    rcases hx with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  exact seekBoundary_cell_step r x hcell left y right

def rawReturnStarted (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) : Result :=
  .running (.returnLeft r)
    (beforeLeftList (returnCells processed remaining) source .markL
      (.markR :: List.replicate available (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external))

def rawReturnedToMark (r : Fin 8) (processed remaining available : ℕ)
    (external source : List ConcreteTape) : Result :=
  .running (.returnLeft r)
    (afterLeftList (returnCells processed remaining) source .markL
      (.markR :: List.replicate available (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external))

theorem rawAtBoundary_zero_rejects (r : Fin 8)
    (processed remaining : ℕ) (external source : List ConcreteTape) :
    run 2 (rawAtBoundary r processed remaining 0 external source) = .rejected := by
  cases processed <;> cases remaining <;>
    simp [rawAtBoundary, seekCells, afterRightList, run,
      seekBoundary_end_step, MStarCopierMicrocode.copierStep,
      MStarCopierMicrocode.copyGo, MStarCopierMicrocode.copyReject,
      MStarParserExecution.applyAction, rightEnd, cellA, cellB,
      List.replicate_succ, List.append_assoc]
  all_goals rfl

theorem reaches_rawReturnStarted_succ (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape) :
    Reaches (rawAtBoundary r processed remaining (available + 1) external source)
      (rawReturnStarted r processed remaining available external source) := by
  refine ⟨2, ?_⟩
  cases processed <;> cases remaining <;>
    simp [run, rawAtBoundary, rawReturnStarted, returnCells, seekCells,
      afterRightList, beforeLeftList, seekBoundary_end_step,
      placeBoundary_step, List.replicate_succ, List.append_assoc]
  all_goals
    rw [← List.append_assoc, ← List.replicate_add]

theorem reaches_rawReturnedToMark (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape) :
    Reaches (rawReturnStarted r processed remaining available external source)
      (rawReturnedToMark r processed remaining available external source) := by
  refine ⟨(returnCells processed remaining).length, ?_⟩
  apply run_left_list_of (.returnLeft r) (returnCells processed remaining)
  intro x hx left y right
  have hcell : x = cellA ∨ x = cellB := by
    simp [returnCells, seekCells] at hx
    aesop
  exact returnLeft_cell_step r x hcell left y right

theorem reaches_rawProcessOne_succ (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape) :
    Reaches (rawRoundStage r processed (remaining + 1) (available + 1)
        external source)
      (rawRoundStage r (processed + 1) remaining available external source) := by
  have h₀ := reaches_rawAtOld r processed remaining (available + 1)
    external source
  have h₁ := reaches_rawSeekStarted r processed remaining (available + 1)
    external source
  have h₂ := reaches_rawAtBoundary r processed remaining (available + 1)
    external source
  have h₃ := reaches_rawReturnStarted_succ r processed remaining available
    external source
  have h₄ := reaches_rawReturnedToMark r processed remaining available
    external source
  have h₅ : Reaches
      (rawReturnedToMark r processed remaining available external source)
      (rawRoundStage r (processed + 1) remaining available external source) := by
    apply reaches_of_oneStep
    cases processed <;>
      simp [rawReturnedToMark, rawRoundStage, returnCells, seekCells,
        afterLeftList, returnLeft_mark_step, List.reverse_append,
        List.replicate_succ, MStarConcreteAlphabet.replicate_cons_rotate,
        List.append_assoc]
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ (reaches_trans h₄ h₅))))

theorem rawRound_canFinish_forces_available_pos (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape)
    (hfinish : CanFinish
      (rawRoundStage r processed (remaining + 1) available external source)) :
    0 < available := by
  by_contra hnot
  have havail : available = 0 := by omega
  subst available
  have hb := canFinish_of_reaches
    (reaches_trans (reaches_rawAtOld r processed remaining 0 external source)
      (reaches_trans (reaches_rawSeekStarted r processed remaining 0 external source)
        (reaches_rawAtBoundary r processed remaining 0 external source))) hfinish
  apply not_canFinish_rejected
  apply canFinish_of_reaches ?_ hb
  exact ⟨2, rawAtBoundary_zero_rejects r processed remaining external source⟩

theorem rawRound_canFinish_consume_one (r : Fin 8)
    (processed remaining available : ℕ)
    (external source : List ConcreteTape)
    (hfinish : CanFinish
      (rawRoundStage r processed (remaining + 1) available external source)) :
    CanFinish (rawRoundStage r (processed + 1) remaining (available - 1)
      external source) := by
  have hpos := rawRound_canFinish_forces_available_pos r processed remaining
    available external source hfinish
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  simpa using canFinish_of_reaches
    (reaches_rawProcessOne_succ r processed remaining rest external source)
    hfinish

/-- Necessary work for one complete physical doubling round. -/
theorem rawRound_canFinish_forces_remaining_le_available (r : Fin 8) :
    ∀ (processed remaining available : ℕ)
      (external source : List ConcreteTape),
      CanFinish (rawRoundStage r processed remaining available external source) →
      remaining ≤ available := by
  intro processed remaining
  induction remaining generalizing processed with
  | zero => intro available external source _; omega
  | succ remaining ih =>
      intro available external source hfinish
      have hpos := rawRound_canFinish_forces_available_pos r processed remaining
        available external source hfinish
      have hnext := rawRound_canFinish_consume_one r processed remaining
        available external source hfinish
      have hle := ih (processed + 1) (available - 1) external source hnext
      omega

theorem rawRound_canFinish_process_all (r : Fin 8) :
    ∀ (processed remaining available : ℕ)
      (external source : List ConcreteTape),
      CanFinish (rawRoundStage r processed remaining available external source) →
      CanFinish (rawRoundStage r (processed + remaining) 0
        (available - remaining) external source) := by
  intro processed remaining
  induction remaining generalizing processed with
  | zero =>
      intro available external source hfinish
      simpa using hfinish
  | succ remaining ih =>
      intro available external source hfinish
      have hnext := rawRound_canFinish_consume_one r processed remaining
        available external source hfinish
      have hle := rawRound_canFinish_forces_remaining_le_available r
        (processed + 1) remaining (available - 1) external source hnext
      have hall := ih (processed + 1) (available - 1) external source hnext
      have hp : processed + (remaining + 1) = processed + 1 + remaining := by
        omega
      have ha : available - (remaining + 1) = available - 1 - remaining := by
        omega
      simpa [hp, ha] using hall

theorem reaches_rawRound_next (r : Fin 8) (n available : ℕ)
    (hn : 0 < n) (hr : r.1 < 7)
    (external source : List ConcreteTape) :
    Reaches (rawRoundStage r n 0 available external source)
      (rawRoundStage (MStarCopierMicrocode.nextRound r hr) 0 (2 * n)
        available external source) := by
  cases n with
  | zero => omega
  | succ n =>
      let tail := List.replicate available
          (.core MStarConcreteAlphabet.work) ++ rightEnd :: external
      have hpos : 0 < n + 1 := by omega
      have h₁ := reaches_normalizeStarted r (n + 1) hpos tail source
      have h₂ := reaches_normalizedAtMark r (n + 1) tail source
      have h₃ := reaches_roundCompleted r (n + 1) tail source
      have h₃' : Reaches (normalizedAtMark r (n + 1) tail source)
          (rawRoundStage (MStarCopierMicrocode.nextRound r hr) 0
            (2 * (n + 1)) available external source) := by
        have htwo : 2 * (n + 1) = (2 * (n + 1) - 1) + 1 := by omega
        unfold roundCompleted at h₃
        rw [dif_pos hr] at h₃
        rw [htwo] at h₃
        unfold rawRoundStage
        rw [htwo]
        simpa [tail, List.replicate_succ, List.append_assoc] using h₃
      have hall := reaches_trans h₁ (reaches_trans h₂ h₃')
      simpa [rawRoundStage, roundStage, tail, List.replicate_succ,
        List.append_assoc] using hall

theorem reaches_rawRound_process_all_of_le (r : Fin 8) :
    ∀ (processed remaining available : ℕ)
      (external source : List ConcreteTape),
      remaining ≤ available →
      Reaches (rawRoundStage r processed remaining available external source)
        (rawRoundStage r (processed + remaining) 0 (available - remaining)
          external source) := by
  intro processed remaining
  induction remaining generalizing processed with
  | zero =>
      intro available external source _
      simpa using reaches_refl
        (rawRoundStage r processed 0 available external source)
  | succ remaining ih =>
      intro available external source hle
      have hpos : 0 < available := by omega
      obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      have hfirst := reaches_rawProcessOne_succ r processed remaining rest
        external source
      have hrest := ih (processed + 1) rest external source (by omega)
      have hall := reaches_trans hfirst hrest
      have hp : processed + (remaining + 1) = processed + 1 + remaining := by
        omega
      have ha : rest + 1 - (remaining + 1) = rest - remaining := by omega
      simpa [hp, ha] using hall

theorem reaches_rawRound_next_of_le (r : Fin 8) (n available : ℕ)
    (hn : 0 < n) (hr : r.1 < 7) (hle : n ≤ available)
    (external source : List ConcreteTape) :
    Reaches (rawRoundStage r 0 n available external source)
      (rawRoundStage (MStarCopierMicrocode.nextRound r hr) 0 (2 * n)
        (available - n) external source) := by
  have hall := reaches_rawRound_process_all_of_le r 0 n available
    external source hle
  have hall' : Reaches (rawRoundStage r 0 n available external source)
      (rawRoundStage r n 0 (available - n) external source) := by
    simpa using hall
  exact reaches_trans hall'
    (reaches_rawRound_next r n (available - n) hn hr external source)

theorem rawRound_canFinish_next (r : Fin 8) (n available : ℕ)
    (hn : 0 < n) (hr : r.1 < 7)
    (external source : List ConcreteTape)
    (hfinish : CanFinish (rawRoundStage r 0 n available external source)) :
    CanFinish (rawRoundStage (MStarCopierMicrocode.nextRound r hr) 0 (2 * n)
      (available - n) external source) := by
  have hall := rawRound_canFinish_process_all r 0 n available external source
    hfinish
  have hall' : CanFinish
      (rawRoundStage r n 0 (available - n) external source) := by
    simpa using hall
  have hnext := canFinish_of_reaches
    (reaches_rawRound_next r n (available - n) hn hr external source) hall'
  simpa using hnext

def rawGroupBlock (source : List ConcreteTape) (n available : ℕ)
    (external : List ConcreteTape) : Result :=
  .running .groupDone
    ⟨source, .markL,
      List.replicate n cellA ++ .markR ::
        List.replicate available (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external⟩

theorem reaches_rawRound_final (n available : ℕ) (hn : 0 < n)
    (external source : List ConcreteTape) :
    Reaches (rawRoundStage (7 : Fin 8) n 0 available external source)
      (rawGroupBlock source (2 * n) available external) := by
  cases n with
  | zero => omega
  | succ n =>
      let tail := List.replicate available
          (.core MStarConcreteAlphabet.work) ++ rightEnd :: external
      have hpos : 0 < n + 1 := by omega
      have h₁ := reaches_normalizeStarted (7 : Fin 8) (n + 1) hpos tail source
      have h₂ := reaches_normalizedAtMark (7 : Fin 8) (n + 1) tail source
      have h₃ := reaches_roundCompleted (7 : Fin 8) (n + 1) tail source
      have h₃' : Reaches (normalizedAtMark (7 : Fin 8) (n + 1) tail source)
          (rawGroupBlock source (2 * (n + 1)) available external) := by
        have htwo : 2 * (n + 1) = (2 * (n + 1) - 1) + 1 := by omega
        unfold roundCompleted at h₃
        rw [dif_neg (by decide)] at h₃
        rw [htwo] at h₃
        unfold rawGroupBlock
        rw [htwo]
        simpa [tail, List.replicate_succ, List.append_assoc] using h₃
      have hall := reaches_trans h₁ (reaches_trans h₂ h₃')
      simpa [rawRoundStage, roundStage, tail, rawGroupBlock,
        List.replicate_succ, List.append_assoc] using hall

def rawGroupedState (bits : List Bool) (done remaining n available : ℕ)
    (junk external : List ConcreteTape) : Result :=
  rawGroupBlock (groupSource bits done remaining junk) n available external

theorem reaches_rawRestart_next_group
    (bits : List Bool) (done remaining n available : ℕ)
    (hn : 0 < n) (junk external : List ConcreteTape) :
    Reaches (rawGroupedState bits done (remaining + 1) n available
        junk external)
      (rawRoundStage (0 : Fin 8) 0 n available external
        (groupSource bits (done + 1) remaining junk)) := by
  let blockRight := List.replicate n cellA ++ .markR ::
    List.replicate available (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external
  have h₀ := reaches_groupSeekStarted bits done remaining junk blockRight
  have h₁ := reaches_groupAtPaired bits done remaining junk blockRight
  have h₂ := reaches_groupReturnStarted bits done remaining junk blockRight
  have h₃ := reaches_groupReturnedToMark bits done remaining junk blockRight
  have h₄ : Reaches
      (groupReturnedToMark bits done remaining junk blockRight)
      (rawRoundStage (0 : Fin 8) 0 n available external
        (groupSource bits (done + 1) remaining junk)) := by
    apply reaches_of_oneStep
    cases n with
    | zero => omega
    | succ n =>
        have hrotate := replicate_cons_rotate
          MStarParserMicrocode.lenDone done
          (List.replicate remaining MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: junk)
        simp [groupReturnedToMark, rawRoundStage, groupSource, groupPrefix,
          blockRight, afterRightList, groupReturn_mark_step,
          List.replicate_succ, List.map_reverse, List.append_assoc,
          List.replicate_add, hrotate]
  have hall := reaches_trans h₀
    (reaches_trans h₁ (reaches_trans h₂ (reaches_trans h₃ h₄)))
  simpa [rawGroupedState, rawGroupBlock, blockRight] using hall

/-- The eight fixed doubling rounds necessarily consume
`1+2+...+128 = 255` work cells.  The remaining buffer is deliberately not
charged here: it is the capacity handed to the group/payload continuation. -/
theorem eightRounds_canFinish_forces_255_le
    (available : ℕ) (external source : List ConcreteTape)
    (h₀ : CanFinish (rawRoundStage (0 : Fin 8) 0 1 available
      external source)) :
    255 ≤ available := by
  let a₁ := available - 1
  let a₂ := a₁ - 2
  let a₃ := a₂ - 4
  let a₄ := a₃ - 8
  let a₅ := a₄ - 16
  let a₆ := a₅ - 32
  let a₇ := a₆ - 64
  have h₁ : CanFinish (rawRoundStage (1 : Fin 8) 0 2 a₁
      external source) := by
    simpa [a₁, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (0 : Fin 8) 1 available (by omega)
        (by decide) external source h₀
  have h₂ : CanFinish (rawRoundStage (2 : Fin 8) 0 4 a₂
      external source) := by
    simpa [a₂, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (1 : Fin 8) 2 a₁ (by omega)
        (by decide) external source h₁
  have h₃ : CanFinish (rawRoundStage (3 : Fin 8) 0 8 a₃
      external source) := by
    simpa [a₃, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (2 : Fin 8) 4 a₂ (by omega)
        (by decide) external source h₂
  have h₄ : CanFinish (rawRoundStage (4 : Fin 8) 0 16 a₄
      external source) := by
    simpa [a₄, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (3 : Fin 8) 8 a₃ (by omega)
        (by decide) external source h₃
  have h₅ : CanFinish (rawRoundStage (5 : Fin 8) 0 32 a₅
      external source) := by
    simpa [a₅, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (4 : Fin 8) 16 a₄ (by omega)
        (by decide) external source h₄
  have h₆ : CanFinish (rawRoundStage (6 : Fin 8) 0 64 a₆
      external source) := by
    simpa [a₆, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (5 : Fin 8) 32 a₅ (by omega)
        (by decide) external source h₅
  have h₇ : CanFinish (rawRoundStage (7 : Fin 8) 0 128 a₇
      external source) := by
    simpa [a₇, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (6 : Fin 8) 64 a₆ (by omega)
        (by decide) external source h₆
  have hlast := rawRound_canFinish_forces_remaining_le_available
    (7 : Fin 8) 0 128 a₇ external source h₇
  dsimp [a₇, a₆, a₅, a₄, a₃, a₂, a₁] at hlast
  omega

theorem eightRounds_canFinish_forces_255_mul_le
    (n available : ℕ) (hn : 0 < n)
    (external source : List ConcreteTape)
    (h₀ : CanFinish (rawRoundStage (0 : Fin 8) 0 n available
      external source)) :
    255 * n ≤ available := by
  let a₁ := available - n
  let a₂ := a₁ - 2 * n
  let a₃ := a₂ - 4 * n
  let a₄ := a₃ - 8 * n
  let a₅ := a₄ - 16 * n
  let a₆ := a₅ - 32 * n
  let a₇ := a₆ - 64 * n
  have h₁ : CanFinish (rawRoundStage (1 : Fin 8) 0 (2 * n) a₁
      external source) := by
    simpa [a₁, MStarCopierMicrocode.nextRound] using
      rawRound_canFinish_next (0 : Fin 8) n available hn
        (by decide) external source h₀
  have h₂ : CanFinish (rawRoundStage (2 : Fin 8) 0 (4 * n) a₂
      external source) := by
    have h := rawRound_canFinish_next (1 : Fin 8) (2 * n) a₁ (by omega)
      (by decide) external source h₁
    simpa [a₂, MStarCopierMicrocode.nextRound,
      show 2 * (2 * n) = 4 * n by ring] using h
  have h₃ : CanFinish (rawRoundStage (3 : Fin 8) 0 (8 * n) a₃
      external source) := by
    have h := rawRound_canFinish_next (2 : Fin 8) (4 * n) a₂ (by omega)
      (by decide) external source h₂
    simpa [a₃, MStarCopierMicrocode.nextRound,
      show 2 * (4 * n) = 8 * n by ring] using h
  have h₄ : CanFinish (rawRoundStage (4 : Fin 8) 0 (16 * n) a₄
      external source) := by
    have h := rawRound_canFinish_next (3 : Fin 8) (8 * n) a₃ (by omega)
      (by decide) external source h₃
    simpa [a₄, MStarCopierMicrocode.nextRound,
      show 2 * (8 * n) = 16 * n by ring] using h
  have h₅ : CanFinish (rawRoundStage (5 : Fin 8) 0 (32 * n) a₅
      external source) := by
    have h := rawRound_canFinish_next (4 : Fin 8) (16 * n) a₄ (by omega)
      (by decide) external source h₄
    simpa [a₅, MStarCopierMicrocode.nextRound,
      show 2 * (16 * n) = 32 * n by ring] using h
  have h₆ : CanFinish (rawRoundStage (6 : Fin 8) 0 (64 * n) a₆
      external source) := by
    have h := rawRound_canFinish_next (5 : Fin 8) (32 * n) a₅ (by omega)
      (by decide) external source h₅
    simpa [a₆, MStarCopierMicrocode.nextRound,
      show 2 * (32 * n) = 64 * n by ring] using h
  have h₇ : CanFinish (rawRoundStage (7 : Fin 8) 0 (128 * n) a₇
      external source) := by
    have h := rawRound_canFinish_next (6 : Fin 8) (64 * n) a₆ (by omega)
      (by decide) external source h₆
    simpa [a₇, MStarCopierMicrocode.nextRound,
      show 2 * (64 * n) = 128 * n by ring] using h
  have hlast := rawRound_canFinish_forces_remaining_le_available
    (7 : Fin 8) 0 (128 * n) a₇ external source h₇
  dsimp [a₇, a₆, a₅, a₄, a₃, a₂, a₁] at hlast
  omega

theorem eightRounds_canFinish_to_rawGroupBlock
    (n available : ℕ) (hn : 0 < n)
    (external source : List ConcreteTape)
    (h₀ : CanFinish (rawRoundStage (0 : Fin 8) 0 n available
      external source)) :
    CanFinish (rawGroupBlock source (256 * n) (available - 255 * n)
      external) := by
  let a₁ := available - n
  let a₂ := a₁ - 2 * n
  let a₃ := a₂ - 4 * n
  let a₄ := a₃ - 8 * n
  let a₅ := a₄ - 16 * n
  let a₆ := a₅ - 32 * n
  let a₇ := a₆ - 64 * n
  have h₁ := rawRound_canFinish_next (0 : Fin 8) n available hn
    (by decide) external source h₀
  have h₂ := rawRound_canFinish_next (1 : Fin 8) (2 * n) a₁ (by omega)
    (by decide) external source (by
      simpa [a₁, MStarCopierMicrocode.nextRound] using h₁)
  have h₃ := rawRound_canFinish_next (2 : Fin 8) (4 * n) a₂ (by omega)
    (by decide) external source (by
      simpa [a₂, MStarCopierMicrocode.nextRound,
        show 2 * (2 * n) = 4 * n by ring] using h₂)
  have h₄ := rawRound_canFinish_next (3 : Fin 8) (8 * n) a₃ (by omega)
    (by decide) external source (by
      simpa [a₃, MStarCopierMicrocode.nextRound,
        show 2 * (4 * n) = 8 * n by ring] using h₃)
  have h₅ := rawRound_canFinish_next (4 : Fin 8) (16 * n) a₄ (by omega)
    (by decide) external source (by
      simpa [a₄, MStarCopierMicrocode.nextRound,
        show 2 * (8 * n) = 16 * n by ring] using h₄)
  have h₆ := rawRound_canFinish_next (5 : Fin 8) (32 * n) a₅ (by omega)
    (by decide) external source (by
      simpa [a₅, MStarCopierMicrocode.nextRound,
        show 2 * (16 * n) = 32 * n by ring] using h₅)
  have h₇raw := rawRound_canFinish_next (6 : Fin 8) (64 * n) a₆ (by omega)
    (by decide) external source (by
      simpa [a₆, MStarCopierMicrocode.nextRound,
        show 2 * (32 * n) = 64 * n by ring] using h₆)
  have h₇ : CanFinish (rawRoundStage (7 : Fin 8) 0 (128 * n) a₇
      external source) := by
    simpa [a₇, MStarCopierMicrocode.nextRound,
      show 2 * (64 * n) = 128 * n by ring] using h₇raw
  have hprocessed := rawRound_canFinish_process_all (7 : Fin 8) 0 (128 * n)
    a₇ external source h₇
  have hprocessed' : CanFinish
      (rawRoundStage (7 : Fin 8) (128 * n) 0 (a₇ - 128 * n)
        external source) := by
    simpa using hprocessed
  have hgroup := canFinish_of_reaches
    (reaches_rawRound_final (128 * n) (a₇ - 128 * n) (by omega)
      external source) hprocessed'
  have hmin := eightRounds_canFinish_forces_255_mul_le n available hn
    external source h₀
  have hrem : a₇ - 128 * n = available - 255 * n := by
    dsimp [a₇, a₆, a₅, a₄, a₃, a₂, a₁]
    omega
  simpa [hrem, show 2 * (128 * n) = 256 * n by ring] using hgroup

theorem reaches_eightRounds_general_of_le
    (n available : ℕ) (hn : 0 < n) (hle : 255 * n ≤ available)
    (external source : List ConcreteTape) :
    Reaches (rawRoundStage (0 : Fin 8) 0 n available external source)
      (rawGroupBlock source (256 * n) (available - 255 * n) external) := by
  let a₁ := available - n
  let a₂ := a₁ - 2 * n
  let a₃ := a₂ - 4 * n
  let a₄ := a₃ - 8 * n
  let a₅ := a₄ - 16 * n
  let a₆ := a₅ - 32 * n
  let a₇ := a₆ - 64 * n
  have h₁ := reaches_rawRound_next_of_le (0 : Fin 8) n available hn
    (by decide) (by omega) external source
  have h₂raw := reaches_rawRound_next_of_le (1 : Fin 8) (2 * n) a₁
    (by omega) (by decide) (by dsimp [a₁]; omega) external source
  have h₂ : Reaches (rawRoundStage (1 : Fin 8) 0 (2 * n) a₁ external source)
      (rawRoundStage (2 : Fin 8) 0 (4 * n) a₂ external source) := by
    simpa [a₂, MStarCopierMicrocode.nextRound,
      show 2 * (2 * n) = 4 * n by ring] using h₂raw
  have h₃raw := reaches_rawRound_next_of_le (2 : Fin 8) (4 * n) a₂
    (by omega) (by decide) (by dsimp [a₂, a₁]; omega) external source
  have h₃ : Reaches (rawRoundStage (2 : Fin 8) 0 (4 * n) a₂ external source)
      (rawRoundStage (3 : Fin 8) 0 (8 * n) a₃ external source) := by
    simpa [a₃, MStarCopierMicrocode.nextRound,
      show 2 * (4 * n) = 8 * n by ring] using h₃raw
  have h₄raw := reaches_rawRound_next_of_le (3 : Fin 8) (8 * n) a₃
    (by omega) (by decide) (by dsimp [a₃, a₂, a₁]; omega) external source
  have h₄ : Reaches (rawRoundStage (3 : Fin 8) 0 (8 * n) a₃ external source)
      (rawRoundStage (4 : Fin 8) 0 (16 * n) a₄ external source) := by
    simpa [a₄, MStarCopierMicrocode.nextRound,
      show 2 * (8 * n) = 16 * n by ring] using h₄raw
  have h₅raw := reaches_rawRound_next_of_le (4 : Fin 8) (16 * n) a₄
    (by omega) (by decide) (by dsimp [a₄, a₃, a₂, a₁]; omega) external source
  have h₅ : Reaches (rawRoundStage (4 : Fin 8) 0 (16 * n) a₄ external source)
      (rawRoundStage (5 : Fin 8) 0 (32 * n) a₅ external source) := by
    simpa [a₅, MStarCopierMicrocode.nextRound,
      show 2 * (16 * n) = 32 * n by ring] using h₅raw
  have h₆raw := reaches_rawRound_next_of_le (5 : Fin 8) (32 * n) a₅
    (by omega) (by decide)
    (by dsimp [a₅, a₄, a₃, a₂, a₁]; omega) external source
  have h₆ : Reaches (rawRoundStage (5 : Fin 8) 0 (32 * n) a₅ external source)
      (rawRoundStage (6 : Fin 8) 0 (64 * n) a₆ external source) := by
    simpa [a₆, MStarCopierMicrocode.nextRound,
      show 2 * (32 * n) = 64 * n by ring] using h₆raw
  have h₇raw := reaches_rawRound_next_of_le (6 : Fin 8) (64 * n) a₆
    (by omega) (by decide)
    (by dsimp [a₆, a₅, a₄, a₃, a₂, a₁]; omega) external source
  have h₇ : Reaches (rawRoundStage (6 : Fin 8) 0 (64 * n) a₆ external source)
      (rawRoundStage (7 : Fin 8) 0 (128 * n) a₇ external source) := by
    simpa [a₇, MStarCopierMicrocode.nextRound,
      show 2 * (64 * n) = 128 * n by ring] using h₇raw
  have hlastProcess := reaches_rawRound_process_all_of_le (7 : Fin 8) 0
    (128 * n) a₇ external source (by
      dsimp [a₇, a₆, a₅, a₄, a₃, a₂, a₁]
      omega)
  have hlastProcess' : Reaches
      (rawRoundStage (7 : Fin 8) 0 (128 * n) a₇ external source)
      (rawRoundStage (7 : Fin 8) (128 * n) 0 (a₇ - 128 * n)
        external source) := by
    simpa using hlastProcess
  have hlast := reaches_trans hlastProcess'
    (reaches_rawRound_final (128 * n) (a₇ - 128 * n) (by omega)
      external source)
  have hrem : a₇ - 128 * n = available - 255 * n := by
    dsimp [a₇, a₆, a₅, a₄, a₃, a₂, a₁]
    omega
  have hall := reaches_trans h₁ (reaches_trans h₂ (reaches_trans h₃
    (reaches_trans h₄ (reaches_trans h₅ (reaches_trans h₆
      (reaches_trans h₇ hlast))))))
  simpa [hrem, show 2 * (128 * n) = 256 * n by ring] using hall

theorem rawGrouped_canFinish_one
    (bits : List Bool) (done remaining n available : ℕ) (hn : 0 < n)
    (junk external : List ConcreteTape)
    (hfinish : CanFinish (rawGroupedState bits done (remaining + 1) n
      available junk external)) :
    255 * n ≤ available ∧
      CanFinish (rawGroupedState bits (done + 1) remaining (256 * n)
        (available - 255 * n) junk external) := by
  have hround := canFinish_of_reaches
    (reaches_rawRestart_next_group bits done remaining n available hn
      junk external) hfinish
  have hmin := eightRounds_canFinish_forces_255_mul_le n available hn
    external (groupSource bits (done + 1) remaining junk) hround
  have hgroup := eightRounds_canFinish_to_rawGroupBlock n available hn
    external (groupSource bits (done + 1) remaining junk) hround
  exact ⟨hmin, by simpa [rawGroupedState] using hgroup⟩

def groupMinimumConsumed : ℕ → ℕ → ℕ
  | 0, _ => 0
  | groups + 1, n => 255 * n + groupMinimumConsumed groups (256 * n)

theorem groupMinimumConsumed_add_width
    (groups n : ℕ) :
    groupMinimumConsumed groups n + n = iteratedGroupWidth groups n := by
  induction groups generalizing n with
  | zero => simp [groupMinimumConsumed, iteratedGroupWidth]
  | succ groups ih =>
      simp only [groupMinimumConsumed, iteratedGroupWidth]
      have h := ih (256 * n)
      omega

theorem rawGrouped_canFinish_fold :
    ∀ (groups : ℕ) (bits : List Bool) (done n available : ℕ),
      0 < n → ∀ (junk external : List ConcreteTape),
      CanFinish (rawGroupedState bits done groups n available junk external) →
      groupMinimumConsumed groups n ≤ available ∧
        CanFinish (rawGroupedState bits (done + groups) 0
          (iteratedGroupWidth groups n)
          (available - groupMinimumConsumed groups n) junk external) := by
  intro groups
  induction groups with
  | zero =>
      intro bits done n available hn junk external hfinish
      exact ⟨by simp [groupMinimumConsumed], by
        simpa [groupMinimumConsumed, iteratedGroupWidth] using hfinish⟩
  | succ groups ih =>
      intro bits done n available hn junk external hfinish
      rcases rawGrouped_canFinish_one bits done groups n available hn
          junk external hfinish with ⟨hfirstMin, hnext⟩
      rcases ih bits (done + 1) (256 * n) (available - 255 * n)
          (by omega) junk external hnext with ⟨hrestMin, htail⟩
      have htotal : groupMinimumConsumed (groups + 1) n ≤ available := by
        simp only [groupMinimumConsumed]
        omega
      refine ⟨htotal, ?_⟩
      have havail : available - 255 * n -
          groupMinimumConsumed groups (256 * n) =
          available - groupMinimumConsumed (groups + 1) n := by
        simp only [groupMinimumConsumed]
        omega
      simpa [iteratedGroupWidth, havail, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail

theorem reaches_rawGrouped_fold_of_le :
    ∀ (groups : ℕ) (bits : List Bool) (done n available : ℕ),
      0 < n → groupMinimumConsumed groups n ≤ available →
      ∀ (junk external : List ConcreteTape),
      Reaches (rawGroupedState bits done groups n available junk external)
        (rawGroupedState bits (done + groups) 0
          (iteratedGroupWidth groups n)
          (available - groupMinimumConsumed groups n) junk external) := by
  intro groups
  induction groups with
  | zero =>
      intro bits done n available hn hle junk external
      simpa [groupMinimumConsumed, iteratedGroupWidth] using
        reaches_refl (rawGroupedState bits done 0 n available junk external)
  | succ groups ih =>
      intro bits done n available hn hle junk external
      have hfirstMin : 255 * n ≤ available := by
        simp only [groupMinimumConsumed] at hle
        omega
      have hrestart := reaches_rawRestart_next_group bits done groups n
        available hn junk external
      have heigth := reaches_eightRounds_general_of_le n available hn
        hfirstMin external (groupSource bits (done + 1) groups junk)
      have hfirst : Reaches
          (rawGroupedState bits done (groups + 1) n available junk external)
          (rawGroupedState bits (done + 1) groups (256 * n)
            (available - 255 * n) junk external) := by
        exact reaches_trans hrestart (by
          simpa [rawGroupedState] using heigth)
      have hrestMin : groupMinimumConsumed groups (256 * n) ≤
          available - 255 * n := by
        simp only [groupMinimumConsumed] at hle
        omega
      have hrest := ih bits (done + 1) (256 * n)
        (available - 255 * n) (by omega) hrestMin junk external
      have hall := reaches_trans hfirst hrest
      have havail : available - 255 * n -
          groupMinimumConsumed groups (256 * n) =
          available - groupMinimumConsumed (groups + 1) n := by
        simp only [groupMinimumConsumed]
        omega
      simpa [iteratedGroupWidth, havail, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

def rawPayloadLoop (copiedRev : List Bool) (processed n : ℕ)
    (todo : List Bool) (available : ℕ)
    (source external : List ConcreteTape) : Result :=
  payloadLoop copiedRev processed n todo source
    (List.replicate available (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)

theorem reaches_rawPayload_one_succ
    (b : Bool) (bs copiedRev : List Bool) (processed n available : ℕ)
    (source external : List ConcreteTape) :
    Reaches (rawPayloadLoop copiedRev processed n (b :: bs) (available + 1)
        source external)
      (rawPayloadLoop (b :: copiedRev) (processed + 1) n bs available
        source external) := by
  cases bs with
  | nil =>
      simpa [rawPayloadLoop, payloadLoop, List.replicate_succ,
        List.append_assoc] using
        (reaches_payload_iteration b copiedRev processed n source
          MStarParserMicrocode.sepLen
          (List.replicate available (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external))
  | cons c cs =>
      simpa [rawPayloadLoop, payloadLoop, List.replicate_succ,
        List.append_assoc] using
        (reaches_payload_iteration b copiedRev processed n
          (cs.map MStarConcreteAlphabet.payloadMarker ++
            MStarParserMicrocode.sepLen :: source)
          (MStarConcreteAlphabet.payloadMarker c)
          (List.replicate available (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external))

theorem rawPayload_zero_rejects
    (b : Bool) (bs copiedRev : List Bool) (processed n : ℕ)
    (source external : List ConcreteTape) :
    ∃ bad, Reaches (rawPayloadLoop copiedRev processed n (b :: bs) 0
        source external) bad ∧ bad = .rejected := by
  let beforeSource := bs.map MStarConcreteAlphabet.payloadMarker ++
    MStarParserMicrocode.sepLen :: source
  have h₀ := reaches_payloadAtSource copiedRev processed n beforeSource
    (MStarConcreteAlphabet.payloadMarker b) (rightEnd :: external)
  have h₁ := reaches_payloadCarryStarted b copiedRev processed n beforeSource
    (rightEnd :: external)
  have h₂ := reaches_payloadAtBoundary b copiedRev processed n beforeSource
    (rightEnd :: external)
  let boundaryState := payloadAtBoundary b copiedRev processed n beforeSource
    (rightEnd :: external)
  have hrejected : run 2 boundaryState = .rejected := by
    cases b <;>
      simp [boundaryState, payloadAtBoundary, afterRightList, run,
        MStarCopierMicrocode.copierStep, MStarCopierMicrocode.copyGo,
        MStarCopierMicrocode.copyReject, MStarParserExecution.applyAction,
        rightEnd, List.append_assoc]
    all_goals rfl
  have hall : Reaches (rawPayloadLoop copiedRev processed n (b :: bs) 0
      source external) boundaryState := by
    have := reaches_trans h₀ (reaches_trans h₁ h₂)
    simpa [rawPayloadLoop, payloadLoop, beforeSource, boundaryState] using this
  exact ⟨.rejected, reaches_trans hall ⟨2, hrejected⟩, rfl⟩

theorem rawPayload_canFinish_forces_length_le :
    ∀ (todo copiedRev : List Bool) (processed n available : ℕ)
      (source external : List ConcreteTape),
      CanFinish (rawPayloadLoop copiedRev processed n todo available
        source external) →
      todo.length ≤ available := by
  intro todo
  induction todo with
  | nil => intro copiedRev processed n available source external _; simp
  | cons b bs ih =>
      intro copiedRev processed n available source external hfinish
      have hpos : 0 < available := by
        by_contra hnot
        have hz : available = 0 := by omega
        subst available
        rcases rawPayload_zero_rejects b bs copiedRev processed n source external with
          ⟨bad, hbad, rfl⟩
        exact not_canFinish_rejected (canFinish_of_reaches hbad hfinish)
      obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      have hnext := canFinish_of_reaches
        (reaches_rawPayload_one_succ b bs copiedRev processed n rest
          source external) hfinish
      have hle := ih (b :: copiedRev) (processed + 1) n rest
        source external hnext
      simp only [List.length_cons]
      omega

theorem reaches_rawPayload_fold_of_le :
    ∀ (todo copiedRev : List Bool) (processed n available : ℕ)
      (source external : List ConcreteTape),
      todo.length ≤ available →
      Reaches (rawPayloadLoop copiedRev processed n todo available source external)
        (rawPayloadLoop (todo.reverse ++ copiedRev) (processed + todo.length)
          n [] (available - todo.length) source external) := by
  intro todo
  induction todo with
  | nil =>
      intro copiedRev processed n available source external hle
      simpa [rawPayloadLoop] using reaches_refl
        (rawPayloadLoop copiedRev processed n [] available source external)
  | cons b bs ih =>
      intro copiedRev processed n available source external hle
      have hlen : 0 < (b :: bs).length := by simp
      have hpos : 0 < available := by omega
      obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      have hfirst := reaches_rawPayload_one_succ b bs copiedRev processed n
        rest source external
      have hbs : bs.length ≤ rest := by
        simp only [List.length_cons] at hle
        omega
      have hrest := ih (b :: copiedRev) (processed + 1) n rest
        source external hbs
      have hall := reaches_trans hfirst hrest
      have havail : rest + 1 - (b :: bs).length = rest - bs.length := by
        simp only [List.length_cons]
        omega
      simpa [List.reverse_cons, havail, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem reaches_rawPayloadDone_groupReady
    (copiedRev : List Bool) (processed n tailWork : ℕ)
    (source external : List ConcreteTape) :
    Reaches (rawPayloadLoop copiedRev processed n [] tailWork source external)
      (.groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (tailWork + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  let boundaryTail := List.replicate tailWork
    (.core MStarConcreteAlphabet.work) ++ rightEnd :: external
  have h₀ := reaches_payloadAtSource copiedRev processed n source
    MStarParserMicrocode.sepLen boundaryTail
  have h₁ := reaches_payloadDoneStarted copiedRev processed n source boundaryTail
  have h₂ := reaches_payloadDoneAtMark copiedRev processed n source boundaryTail
  have h₃ := reaches_finalSeekStarted copiedRev processed n source boundaryTail
  have h₄ := reaches_finalAtBoundary copiedRev processed n source boundaryTail
  have h₅ := PakCopierSlackExecution.reaches_generalFinalReturnStarted
    copiedRev processed n tailWork source external
  have h₆ := PakCopierSlackExecution.reaches_generalFinalAtMark
    copiedRev processed n tailWork source external
  have h₇ := PakCopierSlackExecution.reaches_generalGroupReady
    copiedRev processed n tailWork source external
  have hall := reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ (reaches_trans h₄ (reaches_trans h₅
      (reaches_trans h₆ h₇))))))
  simpa [rawPayloadLoop, payloadLoop, boundaryTail] using hall

theorem reaches_rawGrouped_to_rawPayload_succ
    (x : List Bool) (n available : ℕ) (hn : 0 < n)
    (junk external : List ConcreteTape) :
    Reaches (rawGroupedState x.reverse x.length 0 n (available + 1)
        junk external)
      (rawPayloadLoop [] 0 n x available
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: junk) external) := by
  let sourceTail := List.replicate x.length MStarParserMicrocode.lenDone ++
    MStarParserMicrocode.sepPad :: junk
  let boundaryRight := List.replicate available
    (.core MStarConcreteAlphabet.work) ++ rightEnd :: external
  have hcounter := reaches_counterStarted x.reverse x.length junk n hn
    (.markR :: .core MStarConcreteAlphabet.work :: boundaryRight)
  have hseek := reaches_payloadSeekStarted
    (groupSource x.reverse x.length 0 junk) n hn boundaryRight
  have hall := reaches_trans hcounter hseek
  cases x with
  | nil =>
      simpa [rawGroupedState, rawGroupBlock, rawPayloadLoop, payloadLoop,
        payloadBefore, payloadPath, beforeLeftList,
        sourceTail, boundaryRight, groupSource, groupPrefix,
        List.replicate_succ, List.append_assoc] using hall
  | cons b bs =>
      simpa [rawGroupedState, rawGroupBlock, rawPayloadLoop, payloadLoop,
        payloadBefore, payloadPath, beforeLeftList,
        sourceTail, boundaryRight, groupSource, groupPrefix,
        List.map_reverse, List.replicate_succ, List.append_assoc] using hall

theorem rawGrouped_canFinish_forces_payload_room
    (x : List Bool) (n available : ℕ) (hn : 0 < n)
    (junk external : List ConcreteTape)
    (hfinish : CanFinish
      (rawGroupedState x.reverse x.length 0 n available junk external)) :
    x.length + 1 ≤ available := by
  have hpos : 0 < available := by
    by_contra hnot
    have hz : available = 0 := by omega
    subst available
    have hcounter := reaches_counterStarted x.reverse x.length junk n hn
      (.markR :: rightEnd :: external)
    let source := groupSource x.reverse x.length 0 junk
    have hafterCounter := canFinish_of_reaches (by
      simpa [rawGroupedState, rawGroupBlock] using hcounter) hfinish
    have hreject : Reaches
        (.running .counterToWork
          ⟨.markL :: source, cellA,
            List.replicate (n - 1) cellA ++ .markR :: rightEnd :: external⟩)
        .rejected := by
      -- Convert the unary A block, cross `markR`, then `payloadBoundary`
      -- reads the premature terminal instead of its mandatory first work.
      cases n with
      | zero => omega
      | succ k =>
          refine ⟨k + 3, ?_⟩
          have hrun := run_counterToWork_A (k + 1) (.markL :: source)
            .markR (rightEnd :: external)
          rw [show k + 3 = (k + 1) + 2 by omega, run_add]
          rw [show (.running .counterToWork
              ⟨.markL :: source, cellA,
                List.replicate (k + 1 - 1) cellA ++
                  .markR :: rightEnd :: external⟩ : Result) =
              .running .counterToWork
                (beforeRightRepeat (k + 1) cellA (.markL :: source)
                  .markR (rightEnd :: external)) by
            simp [beforeRightRepeat, List.replicate_succ,
              List.append_assoc]]
          rw [hrun]
          simp [run, afterRightRepeat, counterToWork_mark_step,
            MStarCopierMicrocode.copierStep, MStarCopierMicrocode.copyGo,
            MStarCopierMicrocode.copyReject, MStarParserExecution.applyAction,
            rightEnd, List.append_assoc]
          all_goals rfl
    exact not_canFinish_rejected
      (canFinish_of_reaches hreject hafterCounter)
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hpayload := canFinish_of_reaches
    (reaches_rawGrouped_to_rawPayload_succ x n rest hn junk external) hfinish
  have hle := rawPayload_canFinish_forces_length_le x [] 0 n rest
    (List.replicate x.length MStarParserMicrocode.lenDone ++
      MStarParserMicrocode.sepPad :: junk) external hpayload
  omega

def minimumSuccessfulWorkCount (m : ℕ) : ℕ :=
  iteratedGroupWidth m 256 + m

def consumedBeforeFinalBuffer (m : ℕ) : ℕ :=
  minimumSuccessfulWorkCount m - 1

def actualFinalCapacity (m available : ℕ) : ℕ :=
  available - consumedBeforeFinalBuffer m

def rawCopierSeed (x : List Bool) (available : ℕ)
    (junk external : List ConcreteTape) : Result :=
  .running .seedCell
    ⟨.markL :: groupSource x.reverse 0 x.length junk,
      .core MStarConcreteAlphabet.work,
      .core MStarConcreteAlphabet.work ::
        List.replicate available (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external⟩

theorem reaches_rawCopierSeed_roundZero
    (x : List Bool) (available : ℕ)
    (junk external : List ConcreteTape) :
    Reaches (rawCopierSeed x available junk external)
      (rawRoundStage (0 : Fin 8) 0 1 available external
        (groupSource x.reverse 0 x.length junk)) := by
  exact ⟨4, rfl⟩

/-- Exact necessary reserve for the unchanged copier.  It is one full buffer
smaller than the old sufficient canonical reserve. -/
theorem successful_rawCopier_forces_minimum
    (x : List Bool) (available : ℕ)
    (junk external : List ConcreteTape)
    (hfinish : CanFinish (rawCopierSeed x available junk external)) :
    minimumSuccessfulWorkCount x.length ≤ available := by
  have hround := canFinish_of_reaches
    (reaches_rawCopierSeed_roundZero x available junk external) hfinish
  have hbaseMin := eightRounds_canFinish_forces_255_mul_le 1 available
    (by omega) external (groupSource x.reverse 0 x.length junk) hround
  have hbase := eightRounds_canFinish_to_rawGroupBlock 1 available (by omega)
    external (groupSource x.reverse 0 x.length junk) hround
  have hbase' : CanFinish
      (rawGroupedState x.reverse 0 x.length 256 (available - 255)
        junk external) := by
    simpa [rawGroupedState, show 256 * 1 = 256 by omega] using hbase
  rcases rawGrouped_canFinish_fold x.length x.reverse 0 256
      (available - 255) (by omega) junk external hbase' with
    ⟨hgroupMin, hgroup⟩
  have hpayload := rawGrouped_canFinish_forces_payload_room x
    (iteratedGroupWidth x.length 256)
    (available - 255 - groupMinimumConsumed x.length 256)
    (iteratedGroupWidth_pos x.length 256 (by omega)) junk external (by
      simpa using hgroup)
  have hgroupIdentity := groupMinimumConsumed_add_width x.length 256
  unfold minimumSuccessfulWorkCount
  omega

def rawGeneralCapacityGroupZipper (x : List Bool) (capacity : ℕ)
    (junk external : List ConcreteTape) : Zipper :=
  let R := iteratedGroupWidth x.length 256
  ⟨(.markL :: (doneReturnPrefix x.length).reverse) ++
      MStarParserMicrocode.sepLen ::
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: junk),
    .core MStarConcreteAlphabet.work,
    List.replicate R (.core MStarConcreteAlphabet.work) ++
      x.map coreBit ++
        List.replicate capacity (.core MStarConcreteAlphabet.work) ++
          .markR :: external⟩

theorem reaches_rawCopier_generalCapacity_of_minimum
    (x : List Bool) (available : ℕ)
    (junk external : List ConcreteTape)
    (hmin : minimumSuccessfulWorkCount x.length ≤ available) :
    Reaches (rawCopierSeed x available junk external)
      (.groupReady (rawGeneralCapacityGroupZipper x
        (actualFinalCapacity x.length available) junk external)) := by
  let gmin := groupMinimumConsumed x.length 256
  let afterGroups := available - 255 - gmin
  have hgroupIdentity := groupMinimumConsumed_add_width x.length 256
  have hbaseMin : 255 ≤ available := by
    unfold minimumSuccessfulWorkCount at hmin
    have hR := iteratedGroupWidth_pos x.length 256 (by omega)
    omega
  have hgroupMin : gmin ≤ available - 255 := by
    dsimp [gmin]
    unfold minimumSuccessfulWorkCount at hmin
    omega
  have hroom : x.length + 1 ≤ afterGroups := by
    dsimp [afterGroups, gmin]
    unfold minimumSuccessfulWorkCount at hmin
    omega
  have hseed := reaches_rawCopierSeed_roundZero x available junk external
  have hbase := reaches_eightRounds_general_of_le 1 available (by omega)
    (by simpa using hbaseMin) external (groupSource x.reverse 0 x.length junk)
  have hbase' : Reaches (rawRoundStage (0 : Fin 8) 0 1 available external
        (groupSource x.reverse 0 x.length junk))
      (rawGroupedState x.reverse 0 x.length 256 (available - 255)
        junk external) := by
    simpa [rawGroupedState, show 256 * 1 = 256 by omega] using hbase
  have hgroups := reaches_rawGrouped_fold_of_le x.length x.reverse 0 256
    (available - 255) (by omega) hgroupMin junk external
  have hgroups' : Reaches
      (rawGroupedState x.reverse 0 x.length 256 (available - 255)
        junk external)
      (rawGroupedState x.reverse x.length 0
        (iteratedGroupWidth x.length 256) afterGroups junk external) := by
    simpa [afterGroups, gmin] using hgroups
  have hafterPos : 0 < afterGroups := by omega
  obtain ⟨tailWork, hafter⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hafterPos)
  have hpayloadStart := reaches_rawGrouped_to_rawPayload_succ x
    (iteratedGroupWidth x.length 256) tailWork
    (iteratedGroupWidth_pos x.length 256 (by omega)) junk external
  have hpayloadStart' : Reaches
      (rawGroupedState x.reverse x.length 0
        (iteratedGroupWidth x.length 256) afterGroups junk external)
      (rawPayloadLoop [] 0 (iteratedGroupWidth x.length 256) x tailWork
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: junk) external) := by
    rw [hafter]
    simpa only [Nat.succ_eq_add_one] using hpayloadStart
  have hpayloadLen : x.length ≤ tailWork := by omega
  have hpayload := reaches_rawPayload_fold_of_le x [] 0
    (iteratedGroupWidth x.length 256) tailWork
    (List.replicate x.length MStarParserMicrocode.lenDone ++
      MStarParserMicrocode.sepPad :: junk) external hpayloadLen
  have hpayload' : Reaches
      (rawPayloadLoop [] 0 (iteratedGroupWidth x.length 256) x tailWork
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: junk) external)
      (rawPayloadLoop x.reverse x.length
        (iteratedGroupWidth x.length 256) [] (tailWork - x.length)
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: junk) external) := by
    simpa using hpayload
  have hdone := reaches_rawPayloadDone_groupReady x.reverse x.length
    (iteratedGroupWidth x.length 256) (tailWork - x.length)
    (List.replicate x.length MStarParserMicrocode.lenDone ++
      MStarParserMicrocode.sepPad :: junk) external
  have hall := reaches_trans hseed (reaches_trans hbase' (reaches_trans hgroups'
    (reaches_trans hpayloadStart' (reaches_trans hpayload' hdone))))
  have hcapacity : tailWork - x.length + 1 =
      actualFinalCapacity x.length available := by
    unfold actualFinalCapacity consumedBeforeFinalBuffer
      minimumSuccessfulWorkCount
    dsimp [afterGroups, gmin] at hafter
    omega
  simpa [rawGeneralCapacityGroupZipper, hcapacity] using hall

theorem successful_rawCopier_groupReady_eq_generalCapacity
    (x : List Bool) (available fuel : ℕ)
    (junk external : List ConcreteTape) (out : Zipper)
    (hrun : run fuel (rawCopierSeed x available junk external) =
      .groupReady out) :
    out = rawGeneralCapacityGroupZipper x
      (actualFinalCapacity x.length available) junk external := by
  have hfinish : CanFinish (rawCopierSeed x available junk external) :=
    ⟨fuel, out, hrun⟩
  have hmin := successful_rawCopier_forces_minimum x available junk external
    hfinish
  rcases reaches_rawCopier_generalCapacity_of_minimum x available junk external
      hmin with ⟨canonicalFuel, hcanonical⟩
  exact groupReady_output_unique (rawCopierSeed x available junk external)
    fuel canonicalFuel out
    (rawGeneralCapacityGroupZipper x
      (actualFinalCapacity x.length available) junk external)
    hrun hcanonical

theorem actualFinalCapacity_pos_of_minimum
    {m available : ℕ}
    (h : minimumSuccessfulWorkCount m ≤ available) :
    0 < actualFinalCapacity m available := by
  unfold actualFinalCapacity consumedBeforeFinalBuffer
  have hmin : 0 < minimumSuccessfulWorkCount m := by
    unfold minimumSuccessfulWorkCount
    have hw := iteratedGroupWidth_pos m 256 (by omega)
    omega
  omega

/-- The forward construction's `groupExtraWorkCount` consists of two copies
of every width increment.  This identity exposes the deliberate extra final
buffer in the old canonical reserve. -/
theorem groupExtraWorkCount_add_twice
    (groups n : ℕ) :
    PakSideScannerRow.groupExtraWorkCount groups n + 2 * n =
      2 * iteratedGroupWidth groups n := by
  induction groups generalizing n with
  | zero => simp [PakSideScannerRow.groupExtraWorkCount, iteratedGroupWidth]
  | succ groups ih =>
      simp only [PakSideScannerRow.groupExtraWorkCount, iteratedGroupWidth]
      have h := ih (256 * n)
      omega

theorem copierWorkCount_eq_twice_width_add
    (m : ℕ) :
    PakSideScannerRow.copierWorkCount m =
      2 * iteratedGroupWidth m 256 + m := by
  unfold PakSideScannerRow.copierWorkCount
  have h := groupExtraWorkCount_add_twice m 256
  omega

/-- Canonical reserve = minimum successful reserve + one complete retained
right buffer.  The equality is arithmetic; necessity of the minimum is the
group/payload continuation theorem being assembled below. -/
theorem copierWorkCount_eq_minimum_add_width (m : ℕ) :
    PakSideScannerRow.copierWorkCount m =
      minimumSuccessfulWorkCount m + iteratedGroupWidth m 256 := by
  rw [copierWorkCount_eq_twice_width_add]
  unfold minimumSuccessfulWorkCount
  omega

end PakFixedPolyomino.PakCopierReserveLowerBound
