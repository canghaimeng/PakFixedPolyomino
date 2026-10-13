import PakFixedPolyomino.PakSlotOneMarkRTailProvenance

/-! Original installed-marker residue and actual successful-run tail
provenance with a kernel proof of the literal cellA/markR inequality.
Arbitrary parser-side sources and external tail cells are retained. -/
namespace PakFixedPolyomino.PakSlotOneMarkRTailProvenanceStandard
open MStarCopierMicrocode MStarCopierExecution MStarOuterProgram
open PakSlotOneMarkRTailProvenance

theorem markRResidue_installed
    (source external : List ConcreteTape) :
    MarkRResidue external
      ⟨.markL :: source, cellA, .markR :: external⟩ := by
  refine ⟨[cellA], external, [], ?_, by simp, by simp⟩
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  decide

theorem markRRelocationState_installed
    (source external : List ConcreteTape) :
    MarkRRelocationState external (.findOld 0)
      ⟨.markL :: source, cellA, .markR :: external⟩ :=
  markRResidue_installed source external

theorem liveMarkRRelocationState_installed
    (source external : List ConcreteTape) (fuel : ℕ)
    (out : MStarParserExecution.Zipper ConcreteTape) :
    LiveMarkRRelocationState external fuel (.findOld 0)
      ⟨.markL :: source, cellA, .markR :: external⟩ out := by
  intro _
  exact markRRelocationState_installed source external

theorem run_from_installedMarkR_readsRightEnd_mem_tail
    (source external : List ConcreteTape) (fuel : ℕ)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hsource : .markR ∉ source)
    (hrun : run fuel
      (.running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩) =
        .groupReady out) :
    rightEnd ∈ external := by
  let initial : Result :=
    .running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩
  apply run_from_installedMarkR_readsRightEnd_mem_tail_of_trace
    source external fuel out ?_ hrun
  refine
    { barrier := ?_
      rightBuffer_residue := ?_ }
  · rcases PakSlotOneCopierMarkRBarrier.run_to_groupReady_post_or_crossesMarkR
      fuel (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩ out
      hrun with hpost | hcross
    · simp [PakSlotOneCopierMarkRBarrier.PostRightBuffer] at hpost
    · exact hcross
  · intro j z hj hat
    have htotal : run (j + (fuel - j))
        (.running (.findOld 0)
          ⟨.markL :: source, cellA, .markR :: external⟩) =
        .groupReady out := by
      rw [Nat.add_sub_of_le (Nat.le_of_lt hj)]
      exact hrun
    have hinv := markRRelocationState_at_run external j (fuel - j)
      (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩ out
      .rightBufferScan z (by simp) (markRRelocationState_installed source external)
      (by simpa using hsource) htotal hat
    simpa only [MarkRRelocationState] using hinv.1

end PakFixedPolyomino.PakSlotOneMarkRTailProvenanceStandard
