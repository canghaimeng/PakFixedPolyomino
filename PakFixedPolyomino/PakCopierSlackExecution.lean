import PakFixedPolyomino.PakSideScannerRow

/-! # Copier execution with passive right-buffer slack

The scanner grammar permits the physical `rightEnd` marker to occur after
additional work cells.  The copier accepts this harmless slack and carries it
into the second copied work buffer.  This file records the exact parametric
forward run; it is the correct replacement for the false claim that every
successful copier endpoint is literally the minimum-size canonical zipper.
-/

namespace PakFixedPolyomino.PakCopierSlackExecution

open MStarCopierMicrocode MStarCopierExecution MStarOuterProgram

abbrev ConcreteTape := MStarCopierMicrocode.ConcreteTape
abbrev Zipper := MStarParserExecution.Zipper ConcreteTape
abbrev Result := MStarCopierExecution.Result

def slackFinalSpan (n : ℕ) (copiedRev : List Bool) (slack : ℕ) :
    List ConcreteTape :=
  finalForwardPath n copiedRev ++
    List.replicate (n + 1 + slack) (.core MStarConcreteAlphabet.work)

def slackRightBufferStarted (copiedRev : List Bool) (processed n slack : ℕ)
    (source external : List ConcreteTape) : Result :=
  .running .rightBufferScan
    (beforeRightRepeat (n + slack) (.core MStarConcreteAlphabet.work)
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      rightEnd external)

theorem reaches_slackRightBufferStarted (copiedRev : List Bool)
    (processed n slack : ℕ) (source external : List ConcreteTape) :
    Reaches
      (finalAtBoundary copiedRev processed n source
        (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external))
      (slackRightBufferStarted copiedRev processed n slack source external) := by
  apply reaches_of_oneStep
  cases hsum : n + slack with
  | zero =>
      have hn : n = 0 := by omega
      have hs : slack = 0 := by omega
      subst n
      subst slack
      simp [slackRightBufferStarted, finalAtBoundary, afterRightList,
        beforeRightRepeat, finalSeekBoundary_mark_step]
  | succ k =>
      simp [slackRightBufferStarted, finalAtBoundary, afterRightList,
        beforeRightRepeat, finalSeekBoundary_mark_step, hsum,
        List.replicate_succ, List.append_assoc]

theorem reaches_slackFinalReturnStarted (copiedRev : List Bool)
    (processed n slack : ℕ) (source external : List ConcreteTape) :
    Reaches
      (finalAtBoundary copiedRev processed n source
        (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external))
      (.running .finalReturn
        (beforeLeftList (slackFinalSpan n copiedRev slack).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external))) := by
  have h₀ := reaches_slackRightBufferStarted copiedRev processed n slack
    source external
  have h₁ : Reaches
      (slackRightBufferStarted copiedRev processed n slack source external)
      (.running .rightBufferScan
        (afterRightRepeat (n + slack) (.core MStarConcreteAlphabet.work)
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source)
          rightEnd external)) := by
    refine ⟨n + slack, ?_⟩
    unfold slackRightBufferStarted
    exact run_rightBuffer_work (n + slack)
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      rightEnd external
  have h₂ : Reaches
      (.running .rightBufferScan
        (afterRightRepeat (n + slack) (.core MStarConcreteAlphabet.work)
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source)
          rightEnd external))
      (.running .finalReturn
        (beforeLeftList (slackFinalSpan n copiedRev slack).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external))) := by
    have hwalk : List.replicate (n + slack)
          (.core MStarConcreteAlphabet.work) ++
        .core MStarConcreteAlphabet.work ::
          (finalForwardPath n copiedRev).reverse =
        (slackFinalSpan n copiedRev slack).reverse := by
      have harith : n + 1 + slack = n + slack + 1 := by omega
      simp [slackFinalSpan, harith, List.reverse_append,
        List.replicate_succ, replicate_cons_rotate]
    have hwalk' : List.replicate (n + slack)
          (.core MStarConcreteAlphabet.work) ++
        (.core MStarConcreteAlphabet.work ::
          (finalForwardPath n copiedRev).reverse ++
            .markL :: (doneReturnPrefix processed).reverse ++
              MStarParserMicrocode.sepLen :: source) =
        (slackFinalSpan n copiedRev slack).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source := by
      simpa [List.append_assoc] using congrArg
        (fun xs => xs ++
          (.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)) hwalk
    have hne : (slackFinalSpan n copiedRev slack).reverse ≠ [] := by
      simp [slackFinalSpan, finalForwardPath]
    cases hp : (slackFinalSpan n copiedRev slack).reverse with
    | nil => exact (hne hp).elim
    | cons x xs =>
        apply reaches_of_oneStep
        unfold afterRightRepeat
        rw [hwalk', hp]
        simp [beforeLeftList, hp, rightBufferScan_end_step]
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def slackFinalAtMark (copiedRev : List Bool) (processed n slack : ℕ)
    (source external : List ConcreteTape) : Result :=
  .running .finalReturn
    (afterLeftList (slackFinalSpan n copiedRev slack).reverse
      ((doneReturnPrefix processed).reverse ++
        MStarParserMicrocode.sepLen :: source)
      .markL (.markR :: external))

theorem reaches_slackFinalAtMark (copiedRev : List Bool)
    (processed n slack : ℕ) (source external : List ConcreteTape) :
    Reaches
      (.running .finalReturn
        (beforeLeftList (slackFinalSpan n copiedRev slack).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external)))
      (slackFinalAtMark copiedRev processed n slack source external) := by
  refine ⟨(slackFinalSpan n copiedRev slack).length, ?_⟩
  rw [show (slackFinalSpan n copiedRev slack).length =
      (slackFinalSpan n copiedRev slack).reverse.length by simp]
  apply run_left_list_of .finalReturn (slackFinalSpan n copiedRev slack).reverse
  intro x hx left y right
  have hx' : x ∈ slackFinalSpan n copiedRev slack := by
    simpa using (List.mem_reverse.mp hx)
  have hpass : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one := by
    simp [slackFinalSpan, finalForwardPath] at hx'
    rcases hx' with ⟨-, rfl⟩ | hx | ⟨-, rfl⟩
    · exact Or.inl rfl
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [coreBit]
    · exact Or.inl rfl
  exact finalReturn_pass_step x hpass left y right

theorem reaches_slackGroupReady (copiedRev : List Bool)
    (processed n slack : ℕ) (source external : List ConcreteTape) :
    Reaches (slackFinalAtMark copiedRev processed n slack source external)
      (.groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (n + 1 + slack)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  apply reaches_of_oneStep
  simp [slackFinalAtMark, slackFinalSpan, finalForwardPath, afterLeftList,
    finalReturn_mark_step, List.reverse_append, List.map_reverse,
    List.replicate_succ, List.append_assoc]

/-! The genuinely general final phase: the copied left width `n` and the
number of surviving work cells to the right of the moving barrier are
independent. -/

def generalFinalSpan (n : ℕ) (copiedRev : List Bool) (tailWork : ℕ) :
    List ConcreteTape :=
  finalForwardPath n copiedRev ++
    List.replicate (tailWork + 1) (.core MStarConcreteAlphabet.work)

def generalRightBufferStarted (copiedRev : List Bool)
    (processed n tailWork : ℕ) (source external : List ConcreteTape) : Result :=
  .running .rightBufferScan
    (beforeRightRepeat tailWork (.core MStarConcreteAlphabet.work)
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      rightEnd external)

theorem reaches_generalRightBufferStarted (copiedRev : List Bool)
    (processed n tailWork : ℕ) (source external : List ConcreteTape) :
    Reaches
      (finalAtBoundary copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external))
      (generalRightBufferStarted copiedRev processed n tailWork source external) := by
  apply reaches_of_oneStep
  cases tailWork <;>
    simp [generalRightBufferStarted, finalAtBoundary, afterRightList,
      beforeRightRepeat, finalSeekBoundary_mark_step, List.replicate_succ,
      List.append_assoc]

theorem reaches_generalFinalReturnStarted (copiedRev : List Bool)
    (processed n tailWork : ℕ) (source external : List ConcreteTape) :
    Reaches
      (finalAtBoundary copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external))
      (.running .finalReturn
        (beforeLeftList (generalFinalSpan n copiedRev tailWork).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external))) := by
  have h₀ := reaches_generalRightBufferStarted copiedRev processed n tailWork
    source external
  have h₁ : Reaches
      (generalRightBufferStarted copiedRev processed n tailWork source external)
      (.running .rightBufferScan
        (afterRightRepeat tailWork (.core MStarConcreteAlphabet.work)
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source)
          rightEnd external)) := by
    refine ⟨tailWork, ?_⟩
    unfold generalRightBufferStarted
    exact run_rightBuffer_work tailWork
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      rightEnd external
  have h₂ : Reaches
      (.running .rightBufferScan
        (afterRightRepeat tailWork (.core MStarConcreteAlphabet.work)
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source)
          rightEnd external))
      (.running .finalReturn
        (beforeLeftList (generalFinalSpan n copiedRev tailWork).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external))) := by
    have hwalk : List.replicate tailWork
          (.core MStarConcreteAlphabet.work) ++
        .core MStarConcreteAlphabet.work ::
          (finalForwardPath n copiedRev).reverse =
        (generalFinalSpan n copiedRev tailWork).reverse := by
      simp [generalFinalSpan, List.reverse_append, List.replicate_succ,
        replicate_cons_rotate]
    have hwalk' : List.replicate tailWork
          (.core MStarConcreteAlphabet.work) ++
        (.core MStarConcreteAlphabet.work ::
          (finalForwardPath n copiedRev).reverse ++
            .markL :: (doneReturnPrefix processed).reverse ++
              MStarParserMicrocode.sepLen :: source) =
        (generalFinalSpan n copiedRev tailWork).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source := by
      simpa [List.append_assoc] using congrArg
        (fun xs => xs ++
          (.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)) hwalk
    have hne : (generalFinalSpan n copiedRev tailWork).reverse ≠ [] := by
      simp [generalFinalSpan, finalForwardPath]
    cases hp : (generalFinalSpan n copiedRev tailWork).reverse with
    | nil => exact (hne hp).elim
    | cons x xs =>
        apply reaches_of_oneStep
        unfold afterRightRepeat
        rw [hwalk', hp]
        simp [beforeLeftList, hp, rightBufferScan_end_step]
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def generalFinalAtMark (copiedRev : List Bool)
    (processed n tailWork : ℕ) (source external : List ConcreteTape) : Result :=
  .running .finalReturn
    (afterLeftList (generalFinalSpan n copiedRev tailWork).reverse
      ((doneReturnPrefix processed).reverse ++
        MStarParserMicrocode.sepLen :: source)
      .markL (.markR :: external))

theorem reaches_generalFinalAtMark (copiedRev : List Bool)
    (processed n tailWork : ℕ) (source external : List ConcreteTape) :
    Reaches
      (.running .finalReturn
        (beforeLeftList (generalFinalSpan n copiedRev tailWork).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external)))
      (generalFinalAtMark copiedRev processed n tailWork source external) := by
  refine ⟨(generalFinalSpan n copiedRev tailWork).length, ?_⟩
  rw [show (generalFinalSpan n copiedRev tailWork).length =
      (generalFinalSpan n copiedRev tailWork).reverse.length by simp]
  apply run_left_list_of .finalReturn
    (generalFinalSpan n copiedRev tailWork).reverse
  intro x hx left y right
  have hx' : x ∈ generalFinalSpan n copiedRev tailWork := by
    simpa using (List.mem_reverse.mp hx)
  have hpass : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one := by
    simp [generalFinalSpan, finalForwardPath] at hx'
    rcases hx' with ⟨-, rfl⟩ | hx | ⟨-, rfl⟩
    · exact Or.inl rfl
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [coreBit]
    · exact Or.inl rfl
  exact finalReturn_pass_step x hpass left y right

theorem reaches_generalGroupReady (copiedRev : List Bool)
    (processed n tailWork : ℕ) (source external : List ConcreteTape) :
    Reaches (generalFinalAtMark copiedRev processed n tailWork source external)
      (.groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (tailWork + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  apply reaches_of_oneStep
  simp [generalFinalAtMark, generalFinalSpan, finalForwardPath,
    afterLeftList, finalReturn_mark_step, List.reverse_append,
    List.map_reverse, List.replicate_succ, List.append_assoc]

def slackCopierRoundReserve (m slack : ℕ) (external : List ConcreteTape) :
    List ConcreteTape :=
  eightRoundReserve 1
    (groupExtraReserve m 256
      (List.replicate (m + 1 + slack) (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external))

def slackCopierReserve (m slack : ℕ) (external : List ConcreteTape) :
    List ConcreteTape :=
  .core MStarConcreteAlphabet.work ::
    slackCopierRoundReserve m slack external

theorem slackCopierReserve_eq_work_rightEnd
    (m slack : ℕ) (external : List ConcreteTape) :
    slackCopierReserve m slack external =
      List.replicate
          (PakSideScannerRow.copierWorkCount m + slack)
          (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) ++
        rightEnd :: external := by
  unfold slackCopierReserve slackCopierRoundReserve
    PakSideScannerRow.copierWorkCount
  rw [PakSideScannerRow.eightRoundReserve_eq_replicate,
    PakSideScannerRow.groupExtraReserve_eq_replicate]
  let w : ConcreteTape := .core MStarConcreteAlphabet.work
  change w :: (List.replicate 510 w ++
      (List.replicate (PakSideScannerRow.groupExtraWorkCount m 256) w ++
        (List.replicate (m + 1 + slack) w ++ rightEnd :: external))) =
    List.replicate
        (1 + 510 + PakSideScannerRow.groupExtraWorkCount m 256 + (m + 1) +
          slack) w ++ rightEnd :: external
  have hpref : w :: (List.replicate 510 w ++
      (List.replicate (PakSideScannerRow.groupExtraWorkCount m 256) w ++
        List.replicate (m + 1 + slack) w)) = List.replicate
      (1 + 510 + PakSideScannerRow.groupExtraWorkCount m 256 + (m + 1) +
        slack) w := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp only [List.length_cons, List.length_append, List.length_replicate]
      omega
    · intro a ha
      simp only [List.mem_cons, List.mem_append, List.mem_replicate] at ha
      rcases ha with h | h | h | h
      · exact h
      · exact h.2
      · exact h.2
      · exact h.2
  have hsuffix := congrArg (fun xs => xs ++ rightEnd :: external) hpref
  simpa only [List.cons_append, List.append_assoc] using hsuffix

set_option maxRecDepth 10000 in
theorem reaches_copier_complete_slack (x : List Bool) (slack : ℕ)
    (junk external : List ConcreteTape) :
    let m := x.length
    let n := iteratedGroupWidth m 256
    Reaches
      (.running .seedCell
        ⟨.markL :: groupSource x.reverse 0 m junk,
          .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work ::
            slackCopierReserve m slack external⟩)
      (.groupReady
        ⟨(.markL :: (doneReturnPrefix m).reverse) ++
            MStarParserMicrocode.sepLen ::
              (List.replicate m MStarParserMicrocode.lenDone ++
                MStarParserMicrocode.sepPad :: junk),
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            x.map coreBit ++
              List.replicate (n + 1 + slack)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  dsimp only
  let finalTail : List ConcreteTape :=
    List.replicate (x.length + 1 + slack)
        (.core MStarConcreteAlphabet.work) ++ rightEnd :: external
  let sourceTail : List ConcreteTape :=
    List.replicate x.length MStarParserMicrocode.lenDone ++
      MStarParserMicrocode.sepPad :: junk
  let n := iteratedGroupWidth x.length 256
  have hn : 0 < n := iteratedGroupWidth_pos x.length 256 (by omega)
  have hnshape : n = (n - 1) + 1 := by omega
  have hrep : List.replicate n
        (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) =
      MStarOuterProgram.Tape.core MStarConcreteAlphabet.work ::
        List.replicate (n - 1)
          (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) := by
    rw [hnshape]
    simp [List.replicate_succ]
  have hseed : Reaches
      (.running .seedCell
        ⟨.markL :: groupSource x.reverse 0 x.length junk,
          .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work ::
            slackCopierReserve x.length slack external⟩)
      (roundStage 0 0 1 (slackCopierRoundReserve x.length slack external)
        (groupSource x.reverse 0 x.length junk)) := by
    refine ⟨4, ?_⟩
    simpa [slackCopierReserve, roundStage] using
      (seed_reaches_round_zero_source
        (slackCopierReserve x.length slack external)
        (groupSource x.reverse 0 x.length junk))
  have hbase := reaches_eight_doublings 1 (by omega)
    (groupExtraReserve x.length 256 finalTail)
    (groupSource x.reverse 0 x.length junk)
  have hgroups := reaches_group_fold x.reverse 0 x.length junk 256
    (by omega) finalTail
  have hcounter := reaches_counterStarted x.reverse x.length junk n hn
    (.markR :: List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail)
  have hseek := reaches_payloadSeekStarted
    (groupSource x.reverse x.length 0 junk) n hn
    (List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++ finalTail)
  have hpayload := reaches_payload_fold x [] 0 n sourceTail
    (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hat := reaches_payloadAtSource x.reverse x.length n sourceTail
    MStarParserMicrocode.sepLen
    (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hdone₀ := reaches_payloadDoneStarted x.reverse x.length n sourceTail
    (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hdone₁ := reaches_payloadDoneAtMark x.reverse x.length n sourceTail
    (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hfinal₀ := reaches_finalSeekStarted x.reverse x.length n sourceTail
    (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hfinal₁ := reaches_finalAtBoundary x.reverse x.length n sourceTail
    (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hfinal₂ := reaches_slackFinalReturnStarted x.reverse x.length n slack
    sourceTail external
  have hfinal₃ := reaches_slackFinalAtMark x.reverse x.length n slack
    sourceTail external
  have hready := reaches_slackGroupReady x.reverse x.length n slack
    sourceTail external
  have hbase' : Reaches
      (roundStage 0 0 1 (slackCopierRoundReserve x.length slack external)
        (groupSource x.reverse 0 x.length junk))
      (.running .groupDone
        ⟨groupSource x.reverse 0 x.length junk, .markL,
          List.replicate 256 cellA ++ .markR ::
            List.replicate 256 (.core MStarConcreteAlphabet.work) ++
              groupExtraReserve x.length 256 finalTail⟩) := by
    simpa only [slackCopierRoundReserve, finalTail, Nat.mul_one] using hbase
  have hgroups' : Reaches
      (.running .groupDone
        ⟨groupSource x.reverse 0 x.length junk, .markL,
          List.replicate 256 cellA ++ .markR ::
            List.replicate 256 (.core MStarConcreteAlphabet.work) ++
              groupExtraReserve x.length 256 finalTail⟩)
      (.running .groupDone
        ⟨groupSource x.reverse x.length 0 junk, .markL,
          List.replicate n cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail⟩) := by
    simpa only [Nat.zero_add] using hgroups
  have hcounter' : Reaches
      (.running .groupDone
        ⟨groupSource x.reverse x.length 0 junk, .markL,
          List.replicate n cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail⟩)
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩) := by
    simpa only [hrep, List.append_assoc] using hcounter
  have hright : List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
        finalTail =
      List.replicate x.length (.core MStarConcreteAlphabet.work) ++
        (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external) := by
    dsimp only [finalTail]
    have hnsub : n - 1 + (x.length + 1 + slack) =
        x.length + (n + slack) := by omega
    simp only [← List.append_assoc, ← List.replicate_add]
    rw [hnsub]
  have hseek' : Reaches
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩)
      (payloadLoop [] 0 n x sourceTail
        (List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
          finalTail)) := by
    cases x with
    | nil =>
        simpa [payloadLoop, payloadBefore, payloadPath, sourceTail,
          groupSource, groupPrefix, beforeLeftList, List.replicate_succ,
          List.append_assoc] using hseek
    | cons b bs =>
        simpa [payloadLoop, payloadBefore, payloadPath, sourceTail,
          groupSource, groupPrefix, beforeLeftList, List.map_reverse,
          List.replicate_succ, List.append_assoc] using hseek
  have hseek'' : Reaches
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩)
      (payloadLoop [] 0 n x sourceTail
        (List.replicate x.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external))) := by
    simpa only [hright] using hseek'
  have hpayload' : Reaches
      (payloadLoop [] 0 n x sourceTail
        (List.replicate x.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external)))
      (payloadLoop x.reverse x.length n [] sourceTail
        (List.replicate (n + slack) (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external)) := by
    simpa only [List.append_nil, Nat.zero_add] using hpayload
  have hall := reaches_trans hseed
    (reaches_trans hbase'
      (reaches_trans hgroups'
        (reaches_trans hcounter'
          (reaches_trans hseek''
            (reaches_trans hpayload'
              (reaches_trans hat
                (reaches_trans hdone₀
                  (reaches_trans hdone₁
                    (reaches_trans hfinal₀
                      (reaches_trans hfinal₁
                        (reaches_trans hfinal₂
                          (reaches_trans hfinal₃ hready))))))))))))
  simpa only [sourceTail, n, List.reverse_reverse] using hall

/-- The exact finite seed corresponding to a scanner terminal placed
`slack` work cells after the minimum reserve. -/
def sideSlackCopierSeedZipper (x : ConcretePakSide.Word) (slack : ℕ)
    (external : List ConcreteTape) : Zipper :=
  ⟨.markL :: groupSource x.reverse 0 x.length
      (MStarConcreteAlphabet.pairingPad x.length ++ [.hash]),
    .core MStarConcreteAlphabet.work,
    .core MStarConcreteAlphabet.work ::
      slackCopierReserve x.length slack external⟩

def sideSlackGroupZipper (x : ConcretePakSide.Word) (slack : ℕ)
    (external : List ConcreteTape) : Zipper :=
  let n := iteratedGroupWidth x.length 256
  ⟨(.markL :: (doneReturnPrefix x.length).reverse) ++
      MStarParserMicrocode.sepLen ::
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad ::
            (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])),
    .core MStarConcreteAlphabet.work,
    List.replicate n (.core MStarConcreteAlphabet.work) ++
      x.map coreBit ++
        List.replicate (n + 1 + slack) (.core MStarConcreteAlphabet.work) ++
          .markR :: external⟩

def generalCapacityGroupZipper (x : ConcretePakSide.Word) (capacity : ℕ)
    (external : List ConcreteTape) : Zipper :=
  let n := iteratedGroupWidth x.length 256
  ⟨(.markL :: (doneReturnPrefix x.length).reverse) ++
      MStarParserMicrocode.sepLen ::
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad ::
            (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])),
    .core MStarConcreteAlphabet.work,
    List.replicate n (.core MStarConcreteAlphabet.work) ++
      x.map coreBit ++
        List.replicate capacity (.core MStarConcreteAlphabet.work) ++
          .markR :: external⟩

theorem sideSlackGroupZipper_eq_generalCapacity
    (x : ConcretePakSide.Word) (slack : ℕ)
    (external : List ConcreteTape) :
    sideSlackGroupZipper x slack external =
      generalCapacityGroupZipper x
        (iteratedGroupWidth x.length 256 + 1 + slack) external := by
  rfl

theorem sideSlackCopier_reaches_groupReady
    (x : ConcretePakSide.Word) (slack : ℕ)
    (external : List ConcreteTape) :
    Reaches (.running .seedCell
      (sideSlackCopierSeedZipper x slack external))
      (.groupReady (sideSlackGroupZipper x slack external)) := by
  simpa [sideSlackCopierSeedZipper, sideSlackGroupZipper] using
    reaches_copier_complete_slack x slack
      (MStarConcreteAlphabet.pairingPad x.length ++ [.hash]) external

/-- Determinism turns the parametric forward construction into endpoint
identification for any actual successful run from the same physical seed. -/
theorem successful_sideSlackCopier_groupReady_eq
    (x : ConcretePakSide.Word) (slack fuel : ℕ)
    (external : List ConcreteTape) (out : Zipper)
    (hrun : run fuel (.running .seedCell
      (sideSlackCopierSeedZipper x slack external)) = .groupReady out) :
    out = sideSlackGroupZipper x slack external := by
  rcases sideSlackCopier_reaches_groupReady x slack external with
    ⟨canonicalFuel, hcanonical⟩
  exact groupReady_output_unique
    (.running .seedCell (sideSlackCopierSeedZipper x slack external))
    fuel canonicalFuel out (sideSlackGroupZipper x slack external)
    hrun hcanonical

end PakFixedPolyomino.PakCopierSlackExecution
