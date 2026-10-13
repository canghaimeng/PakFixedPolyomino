import PakFixedPolyomino.PakCopierReserveLowerBound
import PakFixedPolyomino.PakOuterFrontNumericBound
import PakFixedPolyomino.PakCopierGeneralFinalFuel
import Mathlib.Tactic

/-! Exact chronological microfuel of one group restart at every actual
available buffer, then the payload fold/seek/final continuation to
`groupReady`. Restart scans only the left prefix and is independent of
`available`. Extra surviving work after the payload is charged by both
final buffer scans as `2 * slack`. -/

namespace PakFixedPolyomino.PakCopierGeneralGroupPayloadFuel

open MStarCopierMicrocode (cellA rightEnd)
open MStarCopierExecution
open PakCopierReserveLowerBound (rawGroupedState rawPayloadLoop rawRoundStage)
open PakOuterFrontNumericBound (copierGroupRestartFuel copierPayloadFoldFuel
  run_payload_fold)
open PakCopierGeneralFinalFuel (generalFinalFuel run_general_payload_final
  generalFinalFuel_affine_tail)

theorem run_raw_restart_next_group
    (bits : List Bool) (done remaining n available : ℕ)
    (junk external : List MStarCopierMicrocode.ConcreteTape)
    (hn : 0 < n) :
    run (copierGroupRestartFuel bits done)
      (rawGroupedState bits done (remaining + 1) n available junk external) =
      rawRoundStage (0 : Fin 8) 0 n available external
        (groupSource bits (done + 1) remaining junk) := by
  let blockRight : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate n cellA ++ .markR ::
      List.replicate available (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external
  have h0 : run 1
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL, blockRight⟩) =
      groupSeekStarted bits done remaining junk blockRight := by
    change oneStep
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL, blockRight⟩) = _
    simp [groupSource, groupPrefix, groupSeekStarted, beforeLeftList,
      groupDone_step, List.replicate_succ, List.append_assoc]
  have h1 : run (groupPrefix bits done).length
      (groupSeekStarted bits done remaining junk blockRight) =
      groupAtPaired bits done remaining junk blockRight := by
    apply run_left_list_of .groupSeekLen (groupPrefix bits done)
    intro x hx left y right
    have hpass : x = MStarParserMicrocode.endpointMark ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨ x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.lenDone := by
      simp [groupPrefix] at hx
      rcases hx with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    exact groupSeek_pass_step x hpass left y right
  have h2 : run 1
      (groupAtPaired bits done remaining junk blockRight) =
      groupReturnStarted bits done remaining junk blockRight := by
    change oneStep (groupAtPaired bits done remaining junk blockRight) = _
    have hne : (groupPrefix bits done).reverse ≠ [] := by
      simp [groupPrefix]
    cases hrev : (groupPrefix bits done).reverse with
    | nil => exact (hne hrev).elim
    | cons x xs =>
        simp [groupAtPaired, groupReturnStarted, afterLeftList,
          beforeRightList, hrev, groupSeek_paired_step]
  have h3 : run (groupPrefix bits done).length
      (groupReturnStarted bits done remaining junk blockRight) =
      groupReturnedToMark bits done remaining junk blockRight := by
    rw [show (groupPrefix bits done).length =
      (groupPrefix bits done).reverse.length by simp]
    apply run_right_list_of .groupReturn (groupPrefix bits done).reverse
    intro x hx left y right
    have hx' : x ∈ groupPrefix bits done := by
      simpa using (List.mem_reverse.mp hx)
    have hpass : x = MStarParserMicrocode.lenDone ∨
        x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨
        x = MStarParserMicrocode.endpointMark := by
      simp [groupPrefix] at hx'
      rcases hx' with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    exact groupReturn_pass_step x hpass left y right
  have h4 : run 1
      (groupReturnedToMark bits done remaining junk blockRight) =
      rawRoundStage (0 : Fin 8) 0 n available external
        (groupSource bits (done + 1) remaining junk) := by
    cases n with
    | zero => omega
    | succ n =>
        have hrotate := replicate_cons_rotate
          MStarParserMicrocode.lenDone done
          (List.replicate remaining MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: junk)
        have hreturned :
            groupReturnedToMark bits done remaining junk blockRight =
              .running .groupReturn
                ⟨groupSource bits (done + 1) remaining junk, .markL,
                  blockRight⟩ := by
          unfold groupReturnedToMark
          apply congrArg (Result.running .groupReturn)
          apply MStarParserExecution.Zipper.ext
          · simp [afterRightList, groupSource, groupPrefix,
              List.reverse_reverse, List.map_reverse, List.reverse_append,
              List.replicate_succ, List.append_assoc, hrotate]
          · rfl
          · rfl
        rw [hreturned]
        change oneStep
          (.running .groupReturn
            ⟨groupSource bits (done + 1) remaining junk, .markL,
              blockRight⟩) = _
        dsimp [blockRight]
        simpa [rawRoundStage, List.replicate_succ, List.cons_append,
          List.append_assoc] using
          (groupReturn_mark_step
            (groupSource bits (done + 1) remaining junk) cellA
            (List.replicate n cellA ++
              (.markR ::
                (List.replicate available (.core MStarConcreteAlphabet.work) ++
                  rightEnd :: external))))
  have hstart :
      rawGroupedState bits done (remaining + 1) n available junk external =
        .running .groupDone
          ⟨groupSource bits done (remaining + 1) junk, .markL, blockRight⟩ := by
    simp [rawGroupedState, PakCopierReserveLowerBound.rawGroupBlock,
      blockRight, List.append_assoc]
  unfold copierGroupRestartFuel
  rw [hstart, run_add, h0, run_add, h1, run_add, h2, run_add, h3, h4]

theorem run_raw_payload_fold
    (todo copiedRev : List Bool) (processed n available : ℕ)
    (source external : List MStarCopierMicrocode.ConcreteTape)
    (hle : todo.length ≤ available) :
    run (copierPayloadFoldFuel todo copiedRev processed n)
      (rawPayloadLoop copiedRev processed n todo available source external) =
      rawPayloadLoop (todo.reverse ++ copiedRev) (processed + todo.length)
        n [] (available - todo.length) source external := by
  have hsplit :
      List.replicate available (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external =
        List.replicate todo.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate (available - todo.length)
            (.core MStarConcreteAlphabet.work) ++ rightEnd :: external) := by
    calc
      List.replicate available (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external
          = List.replicate (todo.length + (available - todo.length))
              (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external := by
            rw [Nat.add_sub_of_le hle]
      _ = (List.replicate todo.length (.core MStarConcreteAlphabet.work) ++
            List.replicate (available - todo.length)
              (.core MStarConcreteAlphabet.work)) ++
          rightEnd :: external := by
            rw [List.replicate_add]
      _ = List.replicate todo.length (.core MStarConcreteAlphabet.work) ++
            (List.replicate (available - todo.length)
              (.core MStarConcreteAlphabet.work) ++
              rightEnd :: external) := by
            rw [List.append_assoc]
  simp [rawPayloadLoop, hsplit]
  exact run_payload_fold todo copiedRev processed n source
    (List.replicate (available - todo.length)
      (.core MStarConcreteAlphabet.work) ++ rightEnd :: external)

theorem run_raw_payload_at_source
    (copiedRev : List Bool) (processed n tailWork : ℕ)
    (source external : List MStarCopierMicrocode.ConcreteTape) :
    run (payloadPath copiedRev processed n).length
      (rawPayloadLoop copiedRev processed n [] tailWork source external) =
      payloadAtSource copiedRev processed n source
        MStarParserMicrocode.sepLen
        (List.replicate tailWork (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external) := by
  simp [rawPayloadLoop, payloadLoop, payloadBefore]
  apply run_left_list_of .payloadSeek (payloadPath copiedRev processed n)
  intro x hx left y right
  exact payloadSeek_pass_step x
    (payloadPath_seek_pass copiedRev processed n x hx) left y right

def generalPayloadFuel (todo copiedRev : List Bool)
    (processed n available : ℕ) : ℕ :=
  copierPayloadFoldFuel todo copiedRev processed n +
    ((payloadPath (todo.reverse ++ copiedRev)
        (processed + todo.length) n).length +
      generalFinalFuel (todo.reverse ++ copiedRev)
        (processed + todo.length) n (available - todo.length))

theorem run_raw_payload_to_group_ready
    (todo copiedRev : List Bool) (processed n available : ℕ)
    (source external : List MStarCopierMicrocode.ConcreteTape)
    (hle : todo.length ≤ available) :
    run (generalPayloadFuel todo copiedRev processed n available)
      (rawPayloadLoop copiedRev processed n todo available source external) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix (processed + todo.length)).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            (todo.reverse ++ copiedRev).reverse.map coreBit ++
              List.replicate (available - todo.length + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩ := by
  unfold generalPayloadFuel
  rw [run_add,
    run_raw_payload_fold todo copiedRev processed n available source
      external hle,
    run_add,
    run_raw_payload_at_source (todo.reverse ++ copiedRev)
      (processed + todo.length) n (available - todo.length) source external]
  exact run_general_payload_final (todo.reverse ++ copiedRev)
    (processed + todo.length) n (available - todo.length) source external

theorem generalPayloadFuel_affine_available
    (todo copiedRev : List Bool) (processed n available slack : ℕ)
    (hle : todo.length ≤ available) :
    generalPayloadFuel todo copiedRev processed n (available + slack) =
      generalPayloadFuel todo copiedRev processed n available + 2 * slack := by
  have htail : available + slack - todo.length =
      available - todo.length + slack := by
    rw [Nat.add_comm available slack, Nat.add_sub_assoc hle, Nat.add_comm slack]
  simp [generalPayloadFuel, htail, generalFinalFuel_affine_tail]
  ac_rfl

/-- Joint: exact restart at every available, actual payload run, affine slack. -/
def general_group_payload_fuel_spec : Prop :=
  (∀ bits done remaining n available junk external,
    0 < n →
    run (copierGroupRestartFuel bits done)
      (rawGroupedState bits done (remaining + 1) n available junk external) =
      rawRoundStage (0 : Fin 8) 0 n available external
        (groupSource bits (done + 1) remaining junk)) ∧
  (∀ todo copiedRev processed n available source external,
    todo.length ≤ available →
    run (generalPayloadFuel todo copiedRev processed n available)
      (rawPayloadLoop copiedRev processed n todo available source external) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix (processed + todo.length)).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            (todo.reverse ++ copiedRev).reverse.map coreBit ++
              List.replicate (available - todo.length + 1)
                (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) ∧
  (∀ todo copiedRev processed n available slack,
    todo.length ≤ available →
    generalPayloadFuel todo copiedRev processed n (available + slack) =
      generalPayloadFuel todo copiedRev processed n available + 2 * slack)

theorem general_group_payload_fuel_spec_holds :
    general_group_payload_fuel_spec :=
  ⟨run_raw_restart_next_group, run_raw_payload_to_group_ready,
    generalPayloadFuel_affine_available⟩

end PakFixedPolyomino.PakCopierGeneralGroupPayloadFuel
