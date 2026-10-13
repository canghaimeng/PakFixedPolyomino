import PakFixedPolyomino.StandardNondeterministicMachine

/-! Accepting terminal states force a unique component boundary within an
arbitrary raw word, including zero-length paths and repeated zero slots. -/
namespace PakFixedPolyomino.StandardMachineAcceptingPrefixUniqueness
open StandardNondeterministicMachine

theorem accepting_prefix_unique {ns nt nb : Nat} (M : Machine ns nt nb)
    (c d1 d2 : Configuration ns nt) (u1 u2 v1 v2 : List (Fin nb))
    (h1 : run M u1 c=some d1) (ha1 : d1.state=M.accept)
    (h2 : run M u2 c=some d2) (ha2 : d2.state=M.accept)
    (he : u1++v1=u2++v2) : u1=u2 ∧ v1=v2 ∧ d1=d2 := by
  have extension_empty : ∀ (u t : List (Fin nb)) (d : Configuration ns nt),
      run M u c=some d → d.state=M.accept →
      run M (u++t) c≠none → t=[] := by
    intro u t d hu ha hn
    by_contra ht
    apply hn
    rw [run_append,hu,Option.bind_some]
    exact run_accept_nonempty_none M d ha t ht
  have hu : u1=u2 := by
    rcases List.append_eq_append_iff.mp he with ⟨t,ht,_⟩ | ⟨t,ht,_⟩
    · have hn : run M (u1++t) c≠none := by rw [← ht,h2]; simp
      have hz := extension_empty u1 t d1 h1 ha1 hn
      simpa only [hz,List.append_nil] using ht.symm
    · have hn : run M (u2++t) c≠none := by rw [← ht,h1]; simp
      have hz := extension_empty u2 t d2 h2 ha2 hn
      simpa only [hz,List.append_nil] using ht
  subst u2
  exact ⟨rfl,List.append_cancel_left he,Option.some.inj (h1.symm.trans h2)⟩

end PakFixedPolyomino.StandardMachineAcceptingPrefixUniqueness
