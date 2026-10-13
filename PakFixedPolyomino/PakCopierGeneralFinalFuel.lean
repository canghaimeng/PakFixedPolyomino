import PakFixedPolyomino.PakCopierSlackExecution
import Mathlib.Tactic

/-! Exact chronological microfuel of the copier final phase at a general
right-buffer width `tailWork`. The old `copierFinalFuel` ledger used the
canonical buffer `n`. Extra work cells are scanned outward and returned,
so they contribute `2 * tailWork` rather than a free coordinate shift. -/

namespace PakFixedPolyomino.PakCopierGeneralFinalFuel

open MStarCopierExecution
open PakCopierSlackExecution (generalFinalSpan generalRightBufferStarted
  generalFinalAtMark)

/-- Literal phase sum: one-step into done-return, scan `doneReturnPrefix`,
one-step onto the forward path, scan `finalForwardPath`, one-step onto the
right buffer, scan `tailWork` work cells, one-step into final return, scan
`generalFinalSpan`, one-step onto `groupReady`. -/
def generalFinalFuel (copiedRev : List Bool) (processed n tailWork : ℕ) : ℕ :=
  1 + ((doneReturnPrefix processed).length +
    (1 + ((finalForwardPath n copiedRev).length +
      (1 + (tailWork +
        (1 + ((generalFinalSpan n copiedRev tailWork).length + 1)))))))

theorem generalFinalFuel_closed (copiedRev : List Bool)
    (processed n tailWork : ℕ) :
    generalFinalFuel copiedRev processed n tailWork =
      processed + 2 * n + 2 * copiedRev.length + 2 * tailWork + 9 := by
  simp [generalFinalFuel, generalFinalSpan, doneReturnPrefix, finalForwardPath]
  ring

theorem run_general_payload_final (copiedRev : List Bool)
    (processed n tailWork : ℕ)
    (source external : List MStarCopierMicrocode.ConcreteTape) :
    run (generalFinalFuel copiedRev processed n tailWork)
      (payloadAtSource copiedRev processed n source MStarParserMicrocode.sepLen
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (tailWork + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩ := by
  have h0 : run 1
      (payloadAtSource copiedRev processed n source MStarParserMicrocode.sepLen
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      payloadDoneStarted copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    change oneStep
      (payloadAtSource copiedRev processed n source MStarParserMicrocode.sepLen
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) = _
    have hne : doneReturnPrefix processed ≠ [] := by
      simp [doneReturnPrefix]
    cases hp : doneReturnPrefix processed with
    | nil => exact (hne hp).elim
    | cons x xs =>
        unfold payloadAtSource payloadDoneStarted
        simp only [afterLeftList]
        rw [payloadPath_reverse]
        simp [beforeRightList, hp, payloadSeek_sep_step, List.append_assoc]
  have h1 : run (doneReturnPrefix processed).length
      (payloadDoneStarted copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      payloadDoneAtMark copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    apply run_right_list_of .payloadDoneReturn (doneReturnPrefix processed)
    intro x hx left y right
    have hpass : x = MStarParserMicrocode.lenDone ∨
        x = MStarParserMicrocode.endpointMark := by
      simp [doneReturnPrefix] at hx
      rcases hx with ⟨-, rfl⟩ | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact payloadDoneReturn_pass_step x hpass left y right
  have h2 : run 1
      (payloadDoneAtMark copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      finalSeekStarted copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    change oneStep
      (payloadDoneAtMark copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) = _
    have hne : finalForwardPath n copiedRev ≠ [] := by
      simp [finalForwardPath]
    cases hp : finalForwardPath n copiedRev with
    | nil => exact (hne hp).elim
    | cons x xs =>
        simp [payloadDoneAtMark, finalSeekStarted, afterRightList,
          beforeRightList, hp, payloadDoneReturn_mark_step]
  have h3 : run (finalForwardPath n copiedRev).length
      (finalSeekStarted copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      finalAtBoundary copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    apply run_right_list_of .finalSeekBoundary (finalForwardPath n copiedRev)
    intro x hx left y right
    have hpass : x = .core MStarConcreteAlphabet.work ∨
        x = .core MStarConcreteAlphabet.zero ∨
        x = .core MStarConcreteAlphabet.one := by
      simp [finalForwardPath] at hx
      rcases hx with ⟨-, rfl⟩ | hx
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [coreBit]
    exact finalSeekBoundary_pass_step x hpass left y right
  have h4 : run 1
      (finalAtBoundary copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      generalRightBufferStarted copiedRev processed n tailWork source
        external := by
    change oneStep
      (finalAtBoundary copiedRev processed n source
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) = _
    cases tailWork <;>
      simp [generalRightBufferStarted, finalAtBoundary, afterRightList,
        beforeRightRepeat, finalSeekBoundary_mark_step, List.replicate_succ,
        List.append_assoc]
  let scanned : Result :=
    .running .rightBufferScan
      (afterRightRepeat tailWork (.core MStarConcreteAlphabet.work)
        (.core MStarConcreteAlphabet.work ::
          (finalForwardPath n copiedRev).reverse ++ .markL ::
            (doneReturnPrefix processed).reverse ++
              MStarParserMicrocode.sepLen :: source)
        MStarCopierMicrocode.rightEnd external)
  have h5 : run tailWork
      (generalRightBufferStarted copiedRev processed n tailWork source
        external) = scanned := by
    unfold generalRightBufferStarted scanned
    exact run_rightBuffer_work tailWork
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++ .markL ::
          (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      MStarCopierMicrocode.rightEnd external
  let returnStarted : Result :=
    .running .finalReturn
      (beforeLeftList (generalFinalSpan n copiedRev tailWork).reverse
        ((doneReturnPrefix processed).reverse ++
          MStarParserMicrocode.sepLen :: source)
        .markL (.markR :: external))
  have h6 : run 1 scanned = returnStarted := by
    have hwalk : List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          .core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse =
        (generalFinalSpan n copiedRev tailWork).reverse := by
      simp [generalFinalSpan, List.reverse_append, List.replicate_succ]
    have hwalk' : List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++ .markL ::
              (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source) =
        (generalFinalSpan n copiedRev tailWork).reverse ++ .markL ::
          (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source := by
      simpa [List.append_assoc] using congrArg
        (fun xs => xs ++ (.markL :: (doneReturnPrefix processed).reverse ++
          MStarParserMicrocode.sepLen :: source)) hwalk
    have hne : (generalFinalSpan n copiedRev tailWork).reverse ≠ [] := by
      simp [generalFinalSpan, finalForwardPath]
    cases hp : (generalFinalSpan n copiedRev tailWork).reverse with
    | nil => exact (hne hp).elim
    | cons x xs =>
        change oneStep scanned = returnStarted
        unfold scanned returnStarted afterRightRepeat
        rw [hwalk', hp]
        simp [beforeLeftList, rightBufferScan_end_step]
  have h7 : run (generalFinalSpan n copiedRev tailWork).length
      returnStarted =
      generalFinalAtMark copiedRev processed n tailWork source external := by
    unfold returnStarted
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
  have h8 : run 1
      (generalFinalAtMark copiedRev processed n tailWork source external) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (tailWork + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩ := by
    change oneStep
      (generalFinalAtMark copiedRev processed n tailWork source external) = _
    simp [generalFinalAtMark, generalFinalSpan, finalForwardPath,
      afterLeftList, finalReturn_mark_step, List.reverse_append,
      List.map_reverse, List.replicate_succ, List.append_assoc]
  unfold generalFinalFuel
  rw [run_add, h0, run_add, h1, run_add, h2, run_add, h3, run_add, h4,
    run_add, h5, run_add, h6, run_add, h7, h8]

theorem generalFinalFuel_affine_tail (copiedRev : List Bool)
    (processed n tailWork slack : ℕ) :
    generalFinalFuel copiedRev processed n (tailWork + slack) =
      generalFinalFuel copiedRev processed n tailWork + 2 * slack := by
  simp [generalFinalFuel_closed, Nat.mul_add]
  ac_rfl

/-- Joint: closed cost, actual `run` equality, and affine extra-tail law. -/
def general_final_fuel_spec : Prop :=
  (∀ copiedRev processed n tailWork,
    generalFinalFuel copiedRev processed n tailWork =
      processed + 2 * n + 2 * copiedRev.length + 2 * tailWork + 9) ∧
  (∀ copiedRev processed n tailWork source external,
    run (generalFinalFuel copiedRev processed n tailWork)
      (payloadAtSource copiedRev processed n source
        MStarParserMicrocode.sepLen
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (tailWork + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) ∧
  (∀ copiedRev processed n tailWork slack,
    generalFinalFuel copiedRev processed n (tailWork + slack) =
      generalFinalFuel copiedRev processed n tailWork + 2 * slack)

theorem general_final_fuel_spec_holds : general_final_fuel_spec :=
  ⟨generalFinalFuel_closed, run_general_payload_final,
    generalFinalFuel_affine_tail⟩

end PakFixedPolyomino.PakCopierGeneralFinalFuel
