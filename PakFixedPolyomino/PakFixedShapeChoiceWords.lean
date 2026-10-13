import PakFixedPolyomino.PakFixedShapeFirstUncovered

/-! A validated finite-list choice algorithm on the original shape set.
Every tiling has exactly one accepted literal anchor word. Ordinary finite
tape realization and its physical time bound are separate obligations. -/
namespace PakFixedPolyomino.PakFixedShapeChoiceWords
noncomputable section
open TilingAnchoredChoices PakFixedWeightedShapeFamily
open PakFixedShapeAnchoredChoices PakFixedShapeFirstUncovered
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _
abbrev Label := Anchor shapeSupport
abbrev Done := Finset (Placement Shape)

def Fits (n : Nat) (done : Done) (p : Placement Shape) : Prop :=
  Placement.cells shapeSupport p ⊆ square n ∧
    ∀ q ∈ done, Disjoint (Placement.cells shapeSupport p) (Placement.cells shapeSupport q)

instance fitsDecidable (n : Nat) (done : Done) (p : Placement Shape) : Decidable (Fits n done p) := by
  unfold Fits
  infer_instance

def run (n : Nat) : List Label → Done → Option Done
  | [], done => some done
  | a :: slots, done =>
    match firstUncovered n done with
    | none => none
    | some c => if Fits n done (placeAt c a) then run n slots (insert (placeAt c a) done)
                else none

theorem run_cons_some (n : Nat) (a : Label) (slots : List Label) (done out : Done) :
    run n (a :: slots) done = some out ↔
      ∃ c, firstUncovered n done = some c ∧ Fits n done (placeAt c a) ∧
        run n slots (insert (placeAt c a) done) = some out := by
  cases h : firstUncovered n done with
  | none => simp [run,h]
  | some c => by_cases hf : Fits n done (placeAt c a) <;> simp [run,h,hf]

theorem run_subset (n : Nat) (slots : List Label) (done out : Done)
    (hr : run n slots done = some out) : done ⊆ out := by
  induction slots generalizing done with
  | nil =>
    have he : done = out := by simpa [run] using hr
    subst out
    exact Finset.Subset.refl _
  | cons a slots ih =>
    obtain ⟨c,_,_,ht⟩ := (run_cons_some n a slots done out).mp hr
    exact Finset.Subset.trans (Finset.subset_insert _ _) (ih _ ht)

theorem run_card (n : Nat) (slots : List Label) (done out : Done)
    (hr : run n slots done = some out) : out.card = done.card + slots.length := by
  induction slots generalizing done with
  | nil =>
    have he : done = out := by simpa [run] using hr
    subst out
    simp
  | cons a slots ih =>
    obtain ⟨c,hc,_,ht⟩ := (run_cons_some n a slots done out).mp hr
    have hnot := chosen_not_done shapeSupport c (first_some_mem n done c hc) a
    rw [ih _ ht,Finset.card_insert_of_notMem hnot,List.length_cons]
    omega

theorem run_length_le (n : Nat) (slots : List Label) (done out : Done)
    (hr : run n slots done = some out) :
    slots.length ≤ (uncovered shapeSupport (square n) done).card := by
  induction slots generalizing done with
  | nil => simp
  | cons a slots ih =>
    obtain ⟨c,hc,_,ht⟩ := (run_cons_some n a slots done out).mp hr
    have hb := ih _ ht
    have hd := uncovered_strictly_decreases shapeSupport c (first_some_mem n done c hc) a
    simp only [List.length_cons]
    omega

theorem run_square_bound (n : Nat) (slots : List Label) (done out : Done)
    (hr : run n slots done = some out) : slots.length ≤ n^2 :=
  (run_length_le n slots done out hr).trans (uncovered_card_bound n done)

theorem tiling_fits (n : Nat) (T : Tiling shapeSupport (square n))
    (done : Done) (hsub : done ⊆ T.placements) (p : Placement Shape)
    (hp : p ∈ T.placements) (hn : p ∉ done) : Fits n done p := by
  refine ⟨T.placement_subset hp,?_⟩
  intro q hq
  exact T.disjoint hp (hsub hq) (fun h => hn (h ▸ hq))

theorem exists_word (n : Nat) (T : Tiling shapeSupport (square n))
    (done : Done) (hsub : done ⊆ T.placements) :
    ∃ slots : List Label,run n slots done = some T.placements := by
  have aux : ∀ m,∀ done : Done,done ⊆ T.placements →
      (T.placements \ done).card = m → ∃ slots,run n slots done = some T.placements := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro done hsub hm
      cases hc : firstUncovered n done with
      | none =>
        have heq := (first_none_iff_done n T done hsub).mp hc
        exact ⟨[],by simp [run,heq]⟩
      | some c =>
        obtain ⟨a,ha,_⟩ := uncovered_choice_unique shapeSupport T done c (first_some_mem n done c hc)
        let p := placeAt c a
        have hp : p ∈ T.placements \ done := Finset.mem_sdiff.mpr ha
        have he : T.placements \ insert p done = (T.placements \ done).erase p := by
          ext q
          simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
          tauto
        have hlt : (T.placements \ insert p done).card < m := by
          rw [he,← hm]
          exact Finset.card_erase_lt_of_mem hp
        have hs : insert p done ⊆ T.placements := Finset.insert_subset ha.1 hsub
        obtain ⟨slots,ht⟩ := ih _ hlt (insert p done) hs rfl
        exact ⟨a :: slots,(run_cons_some n a slots done T.placements).mpr
          ⟨c,hc,tiling_fits n T done hsub p ha.1 ha.2,ht⟩⟩
  exact aux _ done hsub rfl

theorem word_unique (n : Nat) (T : Tiling shapeSupport (square n))
    (as bs : List Label) (done : Done)
    (ha : run n as done = some T.placements)
    (hb : run n bs done = some T.placements) : as = bs := by
  induction as generalizing bs done with
  | nil =>
    have hca := run_card n [] done T.placements ha
    have hcb := run_card n bs done T.placements hb
    have hz : bs.length = 0 := by simp only [List.length_nil] at hca; omega
    exact (List.length_eq_zero_iff.mp hz).symm
  | cons a as ih =>
    cases bs with
    | nil =>
      have hca := run_card n (a :: as) done T.placements ha
      have hcb := run_card n [] done T.placements hb
      simp only [List.length_cons,List.length_nil] at hca hcb
      omega
    | cons b bs =>
      obtain ⟨c,hc,_,hat⟩ := (run_cons_some n a as done T.placements).mp ha
      obtain ⟨d,hd,_,hbt⟩ := (run_cons_some n b bs done T.placements).mp hb
      have hcd : c = d := Option.some.inj (hc.symm.trans hd)
      subst d
      have hpa := (run_subset n as _ _ hat) (Finset.mem_insert_self _ _)
      have hpb := (run_subset n bs _ _ hbt) (Finset.mem_insert_self _ _)
      have hab : a = b := placeAt_injective shapeSupport c
        (T.cover_unique hpa hpb (placeAt_contains shapeSupport c a) (placeAt_contains shapeSupport c b))
      subst b
      exact congrArg (List.cons a) (ih bs _ hat hbt)

theorem tiling_ext (n : Nat) (T U : Tiling shapeSupport (square n))
    (h : T.placements = U.placements) : T = U := by
  cases T;cases U;cases h;rfl

def AcceptedWord (n : Nat) :=
  {slots : List Label // ∃ T : Tiling shapeSupport (square n),run n slots ∅ = some T.placements}

def wordOfTiling (n : Nat) (T : Tiling shapeSupport (square n)) : AcceptedWord n :=
  ⟨Classical.choose (exists_word n T ∅ (Finset.empty_subset _)),
    ⟨T,Classical.choose_spec (exists_word n T ∅ (Finset.empty_subset _))⟩⟩

def tilingOfWord (n : Nat) (w : AcceptedWord n) : Tiling shapeSupport (square n) :=
  Classical.choose w.property

theorem tilingOfWord_run (n : Nat) (w : AcceptedWord n) :
    run n w.val ∅ = some (tilingOfWord n w).placements := Classical.choose_spec w.property

def tilingWordEquiv (n : Nat) : Tiling shapeSupport (square n) ≃ AcceptedWord n where
  toFun := wordOfTiling n
  invFun := tilingOfWord n
  left_inv T := by
    apply tiling_ext n
    exact Option.some.inj ((tilingOfWord_run n (wordOfTiling n T)).symm.trans
      (Classical.choose_spec (exists_word n T ∅ (Finset.empty_subset _))))
  right_inv w := by
    apply Subtype.ext
    exact word_unique n (tilingOfWord n w) _ _ ∅
      (Classical.choose_spec (exists_word n (tilingOfWord n w) ∅ (Finset.empty_subset _)))
      (tilingOfWord_run n w)

theorem accepted_word_bound (n : Nat) (w : AcceptedWord n) : w.val.length ≤ n^2 :=
  run_square_bound n w.val ∅ _ (tilingOfWord_run n w)

def Partial (n : Nat) (done : Done) : Prop :=
  (∀ p ∈ done,Placement.cells shapeSupport p ⊆ square n) ∧
    Set.Pairwise (↑done : Set (Placement Shape))
      (fun p q => Disjoint (Placement.cells shapeSupport p) (Placement.cells shapeSupport q))

theorem partial_empty (n : Nat) : Partial n ∅ := by
  constructor
  · simp
  · intro p hp
    simp at hp

theorem partial_insert (n : Nat) (done : Done) (p : Placement Shape)
    (hd : Partial n done) (hf : Fits n done p) : Partial n (insert p done) := by
  constructor
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hf.1
    · exact hd.1 q hq
  · intro q hq r hr hqr
    rcases Finset.mem_insert.mp hq with rfl | hqOld
    · rcases Finset.mem_insert.mp hr with rfl | hrOld
      · exact (hqr rfl).elim
      · exact hf.2 r hrOld
    · rcases Finset.mem_insert.mp hr with rfl | hrOld
      · exact (hf.2 q hqOld).symm
      · exact hd.2 hqOld hrOld hqr

theorem partial_run (n : Nat) (slots : List Label) (done out : Done)
    (hd : Partial n done) (hr : run n slots done = some out) : Partial n out := by
  induction slots generalizing done with
  | nil =>
    have he : done = out := by simpa [run] using hr
    exact he ▸ hd
  | cons a slots ih =>
    obtain ⟨c,_,hf,ht⟩ := (run_cons_some n a slots done out).mp hr
    exact ih _ (partial_insert n done (placeAt c a) hd hf) ht

def finish (n : Nat) (done : Done) (hd : Partial n done)
    (hn : firstUncovered n done = none) : Tiling shapeSupport (square n) where
  placements := done
  disjoint := hd.2
  covers := by
    apply Finset.Subset.antisymm
    · intro c hc
      obtain ⟨p,hp,hcp⟩ := Finset.mem_biUnion.mp hc
      exact hd.1 p hp hcp
    · exact Finset.sdiff_eq_empty_iff_subset.mp ((first_none_iff n done).mp hn)

def accepts (n : Nat) (slots : List Label) : Prop :=
  (run n slots ∅).map (firstUncovered n) = some none

theorem accepts_iff_tiling (n : Nat) (slots : List Label) : accepts n slots ↔
    ∃ T : Tiling shapeSupport (square n),run n slots ∅ = some T.placements := by
  constructor
  · intro ha
    cases hr : run n slots ∅ with
    | none => simp [accepts,hr] at ha
    | some out =>
      have hn : firstUncovered n out = none := by simpa [accepts,hr] using ha
      exact ⟨finish n out (partial_run n slots ∅ out (partial_empty n) hr) hn,rfl⟩
  · rintro ⟨T,hr⟩
    have hn := (first_none_iff_done n T T.placements (Finset.Subset.refl _)).mpr rfl
    simp [accepts,hr,hn]

theorem choice_word_spec (n : Nat) :
    (∀ slots,accepts n slots ↔
      ∃ T : Tiling shapeSupport (square n),run n slots ∅ = some T.placements) ∧
    (∀ T : Tiling shapeSupport (square n),∃! slots : List Label,
      run n slots ∅ = some T.placements) ∧
    (∀ slots,accepts n slots → slots.length ≤ n^2) := by
  refine ⟨accepts_iff_tiling n,?_,?_⟩
  · intro T
    obtain ⟨slots,hs⟩ := exists_word n T ∅ (Finset.empty_subset _)
    exact ⟨slots,hs,fun w hw => word_unique n T w slots ∅ hw hs⟩
  · intro slots hs
    obtain ⟨T,hr⟩ := (accepts_iff_tiling n slots).mp hs
    exact run_square_bound n slots ∅ T.placements hr

def RawAcceptedWord (n : Nat) := {slots : List Label // accepts n slots}

def rawWordEquiv (n : Nat) : AcceptedWord n ≃ RawAcceptedWord n where
  toFun w := ⟨w.val,(accepts_iff_tiling n w.val).mpr w.property⟩
  invFun w := ⟨w.val,(accepts_iff_tiling n w.val).mp w.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def rawTilingWordEquiv (n : Nat) : Tiling shapeSupport (square n) ≃ RawAcceptedWord n :=
  (tilingWordEquiv n).trans (rawWordEquiv n)

local instance choiceTilingsFintype (n : Nat) : Fintype (Tiling shapeSupport (square n)) :=
  tilingFintype shapeSupport (square n) shape_nonempty

instance rawWordFintype (n : Nat) : Fintype (RawAcceptedWord n) :=
  Fintype.ofEquiv (Tiling shapeSupport (square n)) (rawTilingWordEquiv n)

theorem squareCount_eq_rawWordCount (n : Nat) :
    squareCount n = Fintype.card (RawAcceptedWord n) := by
  unfold squareCount
  let e := Equiv.cast (congrArg
    (fun d : DecidableEq Shape => @Tiling Shape d shapeSupport (square n))
    (Subsingleton.elim (fun a b => Subtype.instDecidableEq a b) shapeDecidableEq))
  exact Fintype.card_congr (e.trans (rawTilingWordEquiv n))

end
end PakFixedPolyomino.PakFixedShapeChoiceWords
