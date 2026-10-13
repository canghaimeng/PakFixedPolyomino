import PakFixedPolyomino.ULogFiniteTapeUniformMoveReadiness
import PakFixedPolyomino.ULogFiniteTapeGuardedStageComposition
import PakFixedPolyomino.ULogFreshEntry

/-! Real guard and fresh-entry sequencing preserve uniform occupied-slot
moves. The guarded parent and child may both have two occupied labels. -/
namespace PakFixedPolyomino.ULogFiniteTapeComposedUniformMoves
open ULogCompiler ULogFiniteTapeUniformMoveReadiness
open ULogFiniteAlphabetDeterministicRuns (FalseOnly)
variable {ns ms : Nat}

theorem falseOnly_same_moves (p : BoundedProgram ns 3) (hp : FalseOnly p) : SameMoves p := by
  intro q read b c a d hb hc
  cases b with
  | true => rw [hp q read] at hb; contradiction
  | false =>
      cases c with
      | true => rw [hp q read] at hc; contradiction
      | false => exact congrArg BoundedAction.move (Option.some.inj (hb.symm.trans hc))

theorem guarded_same_moves (p : BoundedProgram ns 3) (q : BoundedProgram ms 3)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (hp : SameMoves p) (hq : SameMoves q) :
    SameMoves (ULogFiniteTapeGuardedStageComposition.program p q hns hms handoff) := by
  intro state read b c a d hb hc
  dsimp only [ULogFiniteTapeGuardedStageComposition.program] at hb hc
  by_cases hmax : state.val = ns + ms
  · simp only [hmax, if_pos] at hb hc
    cases b <;> cases c <;> simp_all
  · simp only [hmax, if_false] at hb hc
    by_cases hmid : state.val = ns
    · simp only [hmid, if_pos] at hb hc
      cases b <;> cases c <;> simp_all
    · simp only [hmid, if_false] at hb hc
      by_cases hl : state.val < ns
      · simp only [dif_pos hl] at hb hc
        obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hb
        obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hc
        exact hp _ _ _ _ a0 d0 ha0 hd0
      · simp only [dif_neg hl] at hb hc
        by_cases hr : ns + 2 ≤ state.val ∧ state.val < ns + ms
        · simp only [dif_pos hr] at hb hc
          obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hb
          obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hc
          exact hq _ _ _ _ a0 d0 ha0 hd0
        · simp only [dif_neg hr] at hb
          contradiction

theorem fresh_same_moves {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (hp : SameMoves p) :
    SameMoves (ULogFreshEntry.program p qStart) := by
  intro state read b c a d hb hc
  dsimp only [ULogFreshEntry.program] at hb hc
  by_cases he : state.val = 2
  · simp only [dif_pos he] at hb hc
    cases b <;> cases c <;> simp_all
  · simp only [dif_neg he] at hb hc
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact hp _ _ _ _ a0 d0 ha0 hd0

end PakFixedPolyomino.ULogFiniteTapeComposedUniformMoves
