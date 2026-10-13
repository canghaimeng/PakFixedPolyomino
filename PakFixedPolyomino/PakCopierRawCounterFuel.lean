import PakFixedPolyomino.PakCopierReserveLowerBound
import PakFixedPolyomino.PakOuterFrontNumericBound

/-! Literal costs for the four-step copier seed and for converting the
finished unary counter into the start of the payload loop. Extra available
buffer cells remain actual cells and do not add cost to these phases. -/
namespace PakFixedPolyomino.PakCopierRawCounterFuel
open MStarCopierExecution MStarCopierMicrocode
open PakCopierReserveLowerBound PakOuterFrontNumericBound

theorem run_raw_seed (x : List Bool) (available : Nat)
    (junk external : List MStarCopierMicrocode.ConcreteTape) :
    run 4 (rawCopierSeed x available junk external) =
      rawRoundStage (0 : Fin 8) 0 1 available external
        (groupSource x.reverse 0 x.length junk) := by
  rfl

def rawCounterPayloadFuel (x : List Bool) (n : Nat) : Nat :=
  copierCounterFuel x.reverse x.length + copierPayloadSeekFuel n

theorem rawCounterPayloadFuel_closed (x : List Bool) (n : Nat) :
    rawCounterPayloadFuel x n = 4 * x.length + n + 9 := by
  simp [rawCounterPayloadFuel, copierCounterFuel_closed, copierPayloadSeekFuel]
  ring

theorem run_raw_counter_payload (x : List Bool) (n available : Nat)
    (positive : 0 < n) (junk external : List MStarCopierMicrocode.ConcreteTape) :
    run (rawCounterPayloadFuel x n)
      (rawGroupedState x.reverse x.length 0 n (available + 1) junk external) =
      rawPayloadLoop [] 0 n x available
        (List.replicate x.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: junk) external := by
  let sourceTail := List.replicate x.length MStarParserMicrocode.lenDone ++
    MStarParserMicrocode.sepPad :: junk
  let boundaryRight := List.replicate available (.core MStarConcreteAlphabet.work) ++
    rightEnd :: external
  have counter := run_counter_started x.reverse x.length junk n positive
    (.markR :: .core MStarConcreteAlphabet.work :: boundaryRight)
  have seek := run_payloadSeek_started
    (groupSource x.reverse x.length 0 junk) n positive boundaryRight
  have start := run_add (copierCounterFuel x.reverse x.length) (copierPayloadSeekFuel n)
    (rawGroupedState x.reverse x.length 0 n (available + 1) junk external)
  unfold rawCounterPayloadFuel
  rw [run_add]
  have counter' : run (copierCounterFuel x.reverse x.length)
      (rawGroupedState x.reverse x.length 0 n (available + 1) junk external) =
      .running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++
            .markR :: .core MStarConcreteAlphabet.work :: boundaryRight⟩ := by
    simpa [rawGroupedState, rawGroupBlock, boundaryRight, List.replicate_succ,
      List.append_assoc] using counter
  rw [counter']
  cases x with
  | nil =>
      simpa [rawPayloadLoop, payloadLoop, payloadBefore, payloadPath, beforeLeftList,
        sourceTail, boundaryRight, groupSource, groupPrefix,
        List.replicate_succ, List.append_assoc] using seek
  | cons b bs =>
      simpa [rawPayloadLoop, payloadLoop, payloadBefore, payloadPath, beforeLeftList,
        sourceTail, boundaryRight, groupSource, groupPrefix,
        List.map_reverse, List.replicate_succ, List.append_assoc] using seek

end PakFixedPolyomino.PakCopierRawCounterFuel
