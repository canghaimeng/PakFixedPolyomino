import PakFixedPolyomino.StandardNondeterministicMachine
import Mathlib.Algebra.Ring.GeomSum

/-! Count literal binary transition words of all possible halting lengths.
This bound preserves labels even when two transitions have the same action.
It is a finite cardinality bound, not a bit-time certificate. -/
namespace PakFixedPolyomino.StandardMachineAcceptingCountBound
open StandardNondeterministicMachine

theorem binary_word_code_card (bound : Nat) :
    Fintype.card (WordCode 2 bound) = 2 ^ (bound + 1) - 1 := by
  unfold WordCode
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [Finset.sum_fin_eq_sum_range]
  trans ∑ x ∈ Finset.range (bound + 1), (2 : Nat) ^ x
  · apply Finset.sum_congr rfl
    intro x hx
    have inside : x < bound + 1 := Finset.mem_range.mp hx
    simp [inside]
  · simpa using Nat.geomSum_eq (by decide : 2 ≤ 2) (bound + 1)

theorem accepting_count_le_binary_words {ns nt : Nat}
    (M : Machine ns nt 2) (x : List Bool) (bound : Nat) :
    acceptingCount M x bound ≤ 2 ^ (bound + 1) - 1 := by
  have sub : Fintype.card (AcceptingCode M x bound) ≤ Fintype.card (WordCode 2 bound) :=
    Fintype.card_subtype_le _
  rw [binary_word_code_card] at sub
  exact sub

theorem accepting_count_le_two_pow {ns nt : Nat}
    (M : Machine ns nt 2) (x : List Bool) (bound : Nat) :
    acceptingCount M x bound ≤ 2 ^ (bound + 1) :=
  (accepting_count_le_binary_words M x bound).trans (Nat.sub_le _ _)

end PakFixedPolyomino.StandardMachineAcceptingCountBound
