import PakFixedPolyomino.AnchoredGridMacroData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic

/-!
# Rectangular-dissection census

This file formalizes the two geometric estimates in accepted Danus Fact
`e2a3db2ef9d1d6da` which are consumed by `RectangularDissectionFacts`:

* a nontrivial rectangular partition of the `n × n` grid has at least `n`
  closed macro edges (unit seam segments);
* the number with exactly `i` seam segments is at most `256 ^ i`.

The definitions below refer to literal finite sets.  In particular, no census
bound is retained as a theorem parameter.
-/

namespace PakFixedPolyomino

noncomputable section

namespace RectangularPartition

/-- The literal finite set of closed macro edges (the seam segments). -/
def seamEdges {n : ℕ} (D : RectangularPartition n) : Finset (MacroEdge n) :=
  Finset.univ.filter fun e => ¬ D.IsOpen e

@[simp] theorem mem_seamEdges {n : ℕ} (D : RectangularPartition n)
    (e : MacroEdge n) : e ∈ D.seamEdges ↔ ¬ D.IsOpen e := by
  simp [seamEdges]

/-- `seamCount` really is the cardinality of the literal seam-edge set. -/
theorem card_seamEdges {n : ℕ} (D : RectangularPartition n) :
    D.seamEdges.card = D.seamCount := by
  classical
  unfold seamEdges RectangularPartition.seamCount RectangularPartition.openEdgeCount
  rw [← Fintype.card_subtype (fun e : MacroEdge n => ¬ D.IsOpen e)]
  exact Fintype.card_subtype_compl (fun e : MacroEdge n => D.IsOpen e)

theorem sameBlock_iff_blockAt_eq {n : ℕ} (D : RectangularPartition n)
    (p q : MacroCell n) : D.SameBlock p q ↔ D.blockAt p = D.blockAt q := by
  constructor
  · exact D.blockAt_eq_of_sameBlock
  · intro h
    refine ⟨(D.blockAt p).1, (D.blockAt p).2, D.blockAt_contains p, ?_⟩
    rw [h]
    exact D.blockAt_contains q

private theorem sameBlock_not_of_contains_not_contains {n : ℕ}
    (D : RectangularPartition n) (B : ↑D.blocks) (p q : MacroCell n)
    (hp : B.1.Contains p) (hq : ¬ B.1.Contains q) :
    ¬ D.SameBlock p q := by
  intro h
  have hBp : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
  have hBq : D.blockAt q = B := by
    rw [← hBp]
    exact (D.sameBlock_iff_blockAt_eq p q).mp h |>.symm
  exact hq (hBq ▸ D.blockAt_contains q)

/-- A vertical adjacency in column `x`, between heights `y` and `y+1`. -/
def verticalMacroEdge {n : ℕ} (x : Fin n) (y : Fin (n - 1)) : MacroEdge n :=
  Sum.inr (x, y)

/-- A horizontal adjacency in row `y`, between abscissas `x` and `x+1`. -/
def horizontalMacroEdge {n : ℕ} (x : Fin (n - 1)) (y : Fin n) : MacroEdge n :=
  Sum.inl (x, y)

@[simp] theorem verticalMacroEdge_lo {n : ℕ} (x : Fin n) (y : Fin (n - 1)) :
    (verticalMacroEdge x y).lo =
      (x, ⟨y.1, lt_of_lt_of_le y.2 (Nat.sub_le n 1)⟩) := rfl

@[simp] theorem verticalMacroEdge_hi {n : ℕ} (x : Fin n) (y : Fin (n - 1)) :
    (verticalMacroEdge x y).hi = (x, ⟨y.1 + 1, by omega⟩) := rfl

@[simp] theorem horizontalMacroEdge_lo {n : ℕ} (x : Fin (n - 1)) (y : Fin n) :
    (horizontalMacroEdge x y).lo =
      (⟨x.1, lt_of_lt_of_le x.2 (Nat.sub_le n 1)⟩, y) := rfl

@[simp] theorem horizontalMacroEdge_hi {n : ℕ} (x : Fin (n - 1)) (y : Fin n) :
    (horizontalMacroEdge x y).hi = (⟨x.1 + 1, by omega⟩, y) := rfl

private theorem verticalMacroEdge_injective_left {n : ℕ}
    {f : Fin n → Fin (n - 1)} :
    Function.Injective (fun x => verticalMacroEdge x (f x)) := by
  intro x y h
  simp only [verticalMacroEdge, Sum.inr.injEq, Prod.mk.injEq] at h
  exact h.1

private theorem horizontalMacroEdge_injective_right {n : ℕ}
    (x : Fin (n - 1)) :
    Function.Injective (fun y : Fin n => horizontalMacroEdge x y) := by
  intro y z h
  simp only [horizontalMacroEdge, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

private theorem card_seamEdges_ge_of_vertical_each_column {n : ℕ}
    (D : RectangularPartition n)
    (h : ∀ x : Fin n, ∃ y : Fin (n - 1),
      verticalMacroEdge x y ∈ D.seamEdges) :
    n ≤ D.seamEdges.card := by
  classical
  choose f hf using h
  let g : Fin n → ↑D.seamEdges := fun x => ⟨verticalMacroEdge x (f x), hf x⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply verticalMacroEdge_injective_left (f := f)
    exact congrArg Subtype.val hxy
  have hc := Fintype.card_le_of_injective g hg
  rw [Fintype.card_fin, Fintype.card_coe] at hc
  exact hc

private theorem partition_eq_whole_of_whole_mem {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n)
    (hmem : wholeRectangle n hn ∈ D.blocks) :
    D = wholePartition n hn := by
  apply RectangularPartition.ext
  ext B
  constructor
  · intro hB
    let p : MacroCell n := (B.x₀, B.y₀)
    have hp : B.Contains p := by
      unfold GridRectangle.Contains p
      dsimp
      constructor
      · exact le_rfl
      constructor
      · exact Nat.lt_add_of_pos_right B.width_pos
      · constructor
        · exact le_rfl
        · exact Nat.lt_add_of_pos_right B.height_pos
    have hEq : B = wholeRectangle n hn :=
      (D.unique_block p).unique ⟨hB, hp⟩
        ⟨hmem, wholeRectangle_contains n hn p⟩
    simpa [hEq]
  · intro hB
    simp only [wholePartition_blocks, Finset.mem_singleton] at hB
    subst B
    exact hmem

private theorem full_height_block_has_vertical_side {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (B : ↑D.blocks)
    (hheight : B.1.y₀.1 = 0 ∧ B.1.height.1 = n)
    (hnot : D ≠ wholePartition n hn) :
    (0 < B.1.x₀.1) ∨ (B.1.x₀.1 + B.1.width.1 < n) := by
  have hxb := B.1.x_bound
  by_contra h
  push_neg at h
  have hx0 : B.1.x₀.1 = 0 := by omega
  have hw : B.1.width.1 = n := by omega
  have hBwhole : B.1 = wholeRectangle n hn := by
    apply GridRectangle.ext <;> apply Fin.ext
    · exact hx0
    · exact hheight.1
    · exact hw
    · exact hheight.2
  apply hnot
  apply partition_eq_whole_of_whole_mem hn D
  simpa [hBwhole] using B.2

private theorem card_seamEdges_ge_of_seamless_column {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (hnot : D ≠ wholePartition n hn)
    (x : Fin n)
    (hx : ∀ y : Fin (n - 1), D.IsOpen (verticalMacroEdge x y)) :
    n ≤ D.seamEdges.card := by
  classical
  let p₀ : MacroCell n := (x, ⟨0, hn⟩)
  let B : ↑D.blocks := D.blockAt p₀
  have hB0 : B.1.Contains p₀ := D.blockAt_contains p₀
  have hy0 : B.1.y₀.1 = 0 := by
    unfold GridRectangle.Contains at hB0
    exact Nat.eq_zero_of_le_zero hB0.2.2.1
  have hheight : B.1.height.1 = n := by
    have hle := B.1.y_bound
    rw [hy0, zero_add] at hle
    by_contra hh
    have hlt : B.1.height.1 < n := Nat.lt_of_le_of_ne hle hh
    have hhpos := B.1.height_pos
    let y : Fin (n - 1) := ⟨B.1.height.1 - 1, by omega⟩
    have hlo : B.1.Contains (verticalMacroEdge x y).lo := by
      rw [verticalMacroEdge_lo]
      unfold GridRectangle.Contains
      unfold GridRectangle.Contains at hB0
      dsimp [p₀] at hB0
      have hyv : y.1 = B.1.height.1 - 1 := rfl
      simp only [Prod.fst, Prod.snd]
      omega
    have hhi : ¬ B.1.Contains (verticalMacroEdge x y).hi := by
      rw [verticalMacroEdge_hi]
      unfold GridRectangle.Contains
      have hyv : y.1 = B.1.height.1 - 1 := rfl
      simp only [Prod.fst, Prod.snd]
      omega
    exact (sameBlock_not_of_contains_not_contains D B _ _ hlo hhi) (hx y)
  rcases full_height_block_has_vertical_side hn D B ⟨hy0, hheight⟩ hnot with hleft | hright
  · let bx : Fin (n - 1) := ⟨B.1.x₀.1 - 1, by omega⟩
    let g : Fin n → ↑D.seamEdges := fun y =>
      ⟨horizontalMacroEdge bx y, by
        rw [mem_seamEdges]
        intro hs
        apply sameBlock_not_of_contains_not_contains D B
          (horizontalMacroEdge bx y).hi (horizontalMacroEdge bx y).lo
        · rw [horizontalMacroEdge_hi]
          unfold GridRectangle.Contains
          have hbx : bx.1 = B.1.x₀.1 - 1 := rfl
          simp only [Prod.fst, Prod.snd]
          have hw := B.1.width_pos
          omega
        · rw [horizontalMacroEdge_lo]
          unfold GridRectangle.Contains
          have hbx : bx.1 = B.1.x₀.1 - 1 := rfl
          simp only [Prod.fst, Prod.snd]
          omega
        · exact D.sameBlock_symm hs⟩
    have hg : Function.Injective g := by
      intro y z hyz
      apply horizontalMacroEdge_injective_right bx
      exact congrArg Subtype.val hyz
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc
  · have hw := B.1.width_pos
    let bx : Fin (n - 1) := ⟨B.1.x₀.1 + B.1.width.1 - 1, by omega⟩
    let g : Fin n → ↑D.seamEdges := fun y =>
      ⟨horizontalMacroEdge bx y, by
        rw [mem_seamEdges]
        apply sameBlock_not_of_contains_not_contains D B
        · rw [horizontalMacroEdge_lo]
          unfold GridRectangle.Contains
          have hbx : bx.1 = B.1.x₀.1 + B.1.width.1 - 1 := rfl
          simp only [Prod.fst, Prod.snd]
          omega
        · rw [horizontalMacroEdge_hi]
          unfold GridRectangle.Contains
          have hbx : bx.1 = B.1.x₀.1 + B.1.width.1 - 1 := rfl
          simp only [Prod.fst, Prod.snd]
          omega⟩
    have hg : Function.Injective g := by
      intro y z hyz
      apply horizontalMacroEdge_injective_right bx
      exact congrArg Subtype.val hyz
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc

/-- Fact `e2a3db2ef9d1d6da` (A), for the project's literal partition type. -/
theorem nonwhole_seamCount_ge {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (hnot : D ≠ wholePartition n hn) :
    n ≤ D.seamCount := by
  rw [← D.card_seamEdges]
  by_cases h : ∀ x : Fin n, ∃ y : Fin (n - 1),
      verticalMacroEdge x y ∈ D.seamEdges
  · exact card_seamEdges_ge_of_vertical_each_column D h
  · push_neg at h
    obtain ⟨x, hx⟩ := h
    apply card_seamEdges_ge_of_seamless_column hn D hnot x
    intro y
    by_contra hy
    exact hx y (by simpa [RectangularPartition.mem_seamEdges] using hy)

end RectangularPartition

/-! ## A finite graph traversal used by the census

The following lemma is deliberately about a closed walk rather than an
Eulerian trail.  Every edge is traversed twice.  This is exactly what is
needed to encode an embedded connected edge set by `2m` four-direction
steps, and its proof does not rely on an unformalized Euler theorem.
-/

private theorem tree_has_double_edge_cover
    {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    ∃ (v : V) (p : G.Walk v v),
      p.length = 2 * Nat.card G.edgeSet ∧ p.edgeSet = G.edgeSet := by
  classical
  let motive : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (H : SimpleGraph α), H.IsTree →
      ∃ (v : α) (p : H.Walk v v),
        p.length = 2 * Nat.card H.edgeSet ∧ p.edgeSet = H.edgeSet
  refine Fintype.induction_subsingleton_or_nontrivial (P := motive) V ?_ ?_ G hG
  · intro α _ _ H hH
    haveI : Nonempty α := hH.connected.nonempty
    let v : α := Classical.choice inferInstance
    have hbot : H = ⊥ := Subsingleton.elim H ⊥
    subst H
    exact ⟨v, .nil, by simp⟩
  · intro α _ _ ih H hH
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    obtain ⟨v, hvdeg⟩ := hH.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, hvu, hu⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvdeg
    let S : Set α := {v}ᶜ
    let H' : SimpleGraph S := H.induce S
    have huS : u ∈ S := by
      simp only [S, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hvu.ne.symm
    have hcard : Fintype.card S < Fintype.card α := by
      rw [Fintype.card_compl_set]
      simpa using Nat.sub_lt
        (Fintype.card_pos_iff.mpr hH.connected.nonempty)
        (show 0 < Fintype.card ↑({v} : Set α) by simp)
    have hH' : H'.IsTree := by
      exact ⟨hH.connected.induce_compl_singleton_of_degree_eq_one hvdeg,
        hH.isAcyclic.induce S⟩
    obtain ⟨r, p, hplen, hpedge⟩ := ih S hcard H' hH'
    let u' : S := ⟨u, huS⟩
    have hu_support : u' ∈ p.support := by
      by_cases hru : r = u'
      · simpa [hru] using p.start_mem_support
      · have hreach := hH'.connected.exists_isPath r u'
        obtain ⟨q, hqpath⟩ := hreach
        have hqnil : ¬ q.Nil := by
          intro hnil
          exact hru hnil.eq
        have heG : s(q.penultimate, u') ∈ H'.edgeSet :=
          q.adj_penultimate hqnil
        have hep : s(q.penultimate, u') ∈ p.edges := by
          have : s(q.penultimate, u') ∈ p.edgeSet := by
            rw [hpedge]
            exact heG
          exact this
        exact p.snd_mem_support_of_mem_edges hep
    let pr : H'.Walk u' u' := p.rotate u' hu_support
    have hprlen : pr.length = p.length := by simp [pr]
    have hpredge : pr.edgeSet = H'.edgeSet := by
      apply Set.ext
      intro e
      rw [← hpedge]
      exact (p.rotate_edges u' hu_support).mem_iff
    let incl : H' →g H :=
      ⟨Subtype.val, fun hab => hab⟩
    let q : H.Walk u u := pr.map incl
    have hq_len : q.length = p.length := by simp [q, hprlen]
    have hq_edges : q.edgeSet = H.edgeSet \ H.incidenceSet v := by
      have hmap : q.edgeSet = H'.spanningCoe.edgeSet := by
        simp only [q, SimpleGraph.Walk.edgeSet_map, hpredge]
        exact (SimpleGraph.edgeSet_map
          (Function.Embedding.subtype (fun z => z ∈ S)) H').symm
      have hgraph : H'.spanningCoe = H.deleteIncidenceSet v := by
        ext a b
        rw [SimpleGraph.deleteIncidenceSet_adj]
        change (SimpleGraph.map (Function.Embedding.subtype (fun z => z ∈ S)) H').Adj a b ↔ _
        rw [SimpleGraph.map_adj]
        constructor
        · rintro ⟨a', b', hab, rfl, rfl⟩
          exact ⟨hab, a'.2, b'.2⟩
        · rintro ⟨hab, ha, hb⟩
          exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, rfl, rfl⟩
      rw [hmap, hgraph, H.edgeSet_deleteIncidenceSet]
    let q' : H.Walk u u :=
      SimpleGraph.Walk.cons hvu.symm (SimpleGraph.Walk.cons hvu q)
    refine ⟨u, q', ?_, ?_⟩
    · have hdelcard : Nat.card H'.edgeSet = Nat.card H.edgeSet - 1 := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
          Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
        change H'.edgeFinset.card = H.edgeFinset.card - 1
        rw [H.card_edgeFinset_induce_compl_singleton v,
          H.card_edgeFinset_deleteIncidenceSet v, hvdeg]
      simp only [q', SimpleGraph.Walk.length_cons, hq_len, hplen]
      rw [hdelcard]
      have hedgepos : 0 < Nat.card H.edgeSet := by
        rw [Nat.card_coe_set_eq, Set.ncard_pos]
        exact ⟨s(v, u), hvu⟩
      omega
    · have hincFin : H.incidenceFinset v = {s(v, u)} := by
        have hcard : (H.incidenceFinset v).card = 1 := by
          simpa using hvdeg
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
        have he0 : s(v, u) ∈ H.incidenceFinset v := by
          rw [H.mem_incidenceFinset, H.mem_incidenceSet]
          exact hvu
        rw [he, Finset.mem_singleton] at he0
        simpa [he0]
      have hinc : H.incidenceSet v = {s(v, u)} := by
        ext e
        have he := congrArg (fun F : Finset (Sym2 α) => e ∈ F) hincFin
        simpa using he
      simp only [q', SimpleGraph.Walk.edgeSet_cons, hq_edges, hinc]
      rw [show s(u, v) = s(v, u) by exact Sym2.eq_swap]
      let e : Sym2 α := s(v, u)
      change insert e (insert e (H.edgeSet \ {e})) = H.edgeSet
      rw [Set.insert_idem, Set.insert_sdiff_singleton]
      exact Set.insert_eq_of_mem hvu

private theorem edge_cover_walk_visits_every_vertex
    {V : Type} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) {r : V} (p : G.Walk r r)
    (hp : p.edgeSet = G.edgeSet) : ∀ v : V, v ∈ p.support := by
  intro v
  by_cases hrv : r = v
  · simpa [← hrv] using p.start_mem_support
  · obtain ⟨q, hqpath⟩ := hG.exists_isPath r v
    have hqnil : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne hrv
    have heG : s(q.penultimate, v) ∈ G.edgeSet := q.adj_penultimate hqnil
    have hep : s(q.penultimate, v) ∈ p.edges := by
      have : s(q.penultimate, v) ∈ p.edgeSet := by simpa [hp] using heG
      exact this
    exact p.snd_mem_support_of_mem_edges hep

private theorem insert_edge_detour
    {V : Type} [DecidableEq V] {G : SimpleGraph V} {r : V} (p : G.Walk r r)
    (hall : ∀ v : V, v ∈ p.support) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ (r' : V) (q : G.Walk r' r'),
      q.length = p.length + 2 ∧ q.edgeSet = insert e p.edgeSet ∧
        ∀ v : V, v ∈ q.support := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := he
      let pr : G.Walk a a := p.rotate a (hall a)
      let q : G.Walk a a :=
        SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hab.symm pr)
      refine ⟨a, q, ?_, ?_, ?_⟩
      · simp [q, pr]
      · simp only [q, SimpleGraph.Walk.edgeSet_cons]
        rw [show s(b, a) = s(a, b) by exact Sym2.eq_swap, Set.insert_idem]
        apply congrArg (insert s(a, b))
        apply Set.ext
        intro x
        simp only [SimpleGraph.Walk.mem_edgeSet]
        exact (p.rotate_edges a (hall a)).mem_iff
      · intro v
        simp only [q, SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr (Or.inr (by simpa [pr] using hall v))

/-- Every finite connected simple graph has a closed walk of length twice its
edge count whose edge set is the entire graph.  This is the precise finite
replacement for the doubled-edge Euler-tour sentence in Fact
`e2a3db2ef9d1d6da`. -/
private theorem connected_has_double_edge_cover
    {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ (v : V) (p : G.Walk v v),
      p.length = 2 * Nat.card G.edgeSet ∧ p.edgeSet = G.edgeSet := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  obtain ⟨r₀, pT, hpTlen, hpTedge⟩ := tree_has_double_edge_cover T hT
  let p₀ : G.Walk r₀ r₀ := pT.mapLe hTG
  have hp₀len : p₀.length = 2 * Nat.card T.edgeSet := by simpa [p₀] using hpTlen
  have hp₀edge : p₀.edgeSet = T.edgeSet := by simpa [p₀] using hpTedge
  have hp₀all : ∀ v : V, v ∈ p₀.support := by
    intro v
    simpa [p₀] using edge_cover_walk_visits_every_vertex hT.connected pT hpTedge v
  let extra : Finset (Sym2 V) := G.edgeFinset \ T.edgeFinset
  have hextra : extra ⊆ G.edgeFinset := Finset.sdiff_subset
  have build : ∀ E : Finset (Sym2 V), E ⊆ G.edgeFinset →
      ∃ (r : V) (p : G.Walk r r),
        p.length = p₀.length + 2 * E.card ∧
        p.edgeSet = p₀.edgeSet ∪ (E : Set (Sym2 V)) ∧
        ∀ v : V, v ∈ p.support := by
    intro E hEG
    induction E using Finset.induction_on with
    | empty => exact ⟨r₀, p₀, by simp, by simp, hp₀all⟩
    | @insert e E heE ih =>
        have hEsub : E ⊆ G.edgeFinset := fun x hx => hEG (Finset.mem_insert_of_mem hx)
        obtain ⟨r, p, hplen, hpedge, hpall⟩ := ih hEsub
        have heG : e ∈ G.edgeSet := by
          rw [← G.mem_edgeFinset]
          exact hEG (Finset.mem_insert_self e E)
        obtain ⟨r', q, hqlen, hqedge, hqall⟩ := insert_edge_detour p hpall e heG
        refine ⟨r', q, ?_, ?_, hqall⟩
        · rw [hqlen, hplen, Finset.card_insert_of_notMem heE]
          omega
        · rw [hqedge, hpedge]
          ext x
          simp
  obtain ⟨r, p, hplen, hpedge, -⟩ := build extra hextra
  refine ⟨r, p, ?_, ?_⟩
  · rw [hplen, hp₀len]
    have hcard : extra.card = G.edgeFinset.card - T.edgeFinset.card := by
      exact Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hTG)
    have hTcard : Nat.card T.edgeSet = T.edgeFinset.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
      rfl
    have hGcard : Nat.card G.edgeSet = G.edgeFinset.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
      rfl
    rw [hcard, hTcard, hGcard]
    have hle : T.edgeFinset.card ≤ G.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hTG)
    omega
  · rw [hpedge, hp₀edge]
    apply Set.ext
    intro e
    simp only [extra, Finset.coe_sdiff, Finset.coe_sort_coe, Set.mem_union,
      Set.mem_sdiff, Set.mem_setOf_eq]
    constructor
    · intro he
      rcases he with heT | heG
      · exact SimpleGraph.edgeSet_mono hTG heT
      · simpa using heG.1
    · intro he
      by_cases heT : e ∈ T.edgeSet
      · exact Or.inl heT
      · apply Or.inr
        constructor
        · simpa using he
        · simpa using heT

/-! ## Unit-segment graphs and their four-direction codes -/

abbrev GridVertex (n : ℕ) := Fin (n + 1) × Fin (n + 1)

/-- The actual lattice segment dual to a macro adjacency. -/
def macroSegment {n : ℕ} : MacroEdge n → Sym2 Cell
  | .inl e => s((((e.1.1 + 1 : ℕ) : ℤ), (e.2.1 : ℤ)),
      (((e.1.1 + 1 : ℕ) : ℤ), ((e.2.1 + 1 : ℕ) : ℤ)))
  | .inr e => s(((e.1.1 : ℤ), ((e.2.1 + 1 : ℕ) : ℤ)),
      (((e.1.1 + 1 : ℕ) : ℤ), ((e.2.1 + 1 : ℕ) : ℤ)))

theorem macroSegment_injective {n : ℕ} :
    Function.Injective (@macroSegment n) := by
  intro e f
  rcases e with e | e <;> rcases f with f | f <;>
    simp [macroSegment, Sym2.eq, Prod.ext_iff, Sum.inl.injEq, Sum.inr.injEq] <;>
    omega

theorem macroSegment_not_diag {n : ℕ} (e : MacroEdge n) :
    macroSegment e ∉ (Sym2.diagSet : Set (Sym2 Cell)) := by
  rcases e with e | e <;>
    simp [macroSegment, Sym2.mem_diagSet, Prod.ext_iff] <;> omega

/-- The finite grid graph whose edge set is exactly `M`'s unit segments. -/
def segmentGraph {n : ℕ} (M : Finset (MacroEdge n)) :
    SimpleGraph Cell :=
  SimpleGraph.fromEdgeSet (macroSegment '' (M : Set (MacroEdge n)))

theorem segmentGraph_edgeSet {n : ℕ} (M : Finset (MacroEdge n)) :
    (segmentGraph M).edgeSet = macroSegment '' (M : Set (MacroEdge n)) := by
  rw [segmentGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun h => h.1
  · intro he
    refine ⟨he, ?_⟩
    rintro hdiag
    rcases he with ⟨f, -, rfl⟩
    exact macroSegment_not_diag f hdiag

theorem segmentGraph_edge_card {n : ℕ} (M : Finset (MacroEdge n)) :
    Nat.card (segmentGraph M).edgeSet = M.card := by
  rw [segmentGraph_edgeSet]
  calc
    Nat.card (macroSegment '' (M : Set (MacroEdge n))) =
        (macroSegment '' (M : Set (MacroEdge n))).ncard := rfl
    _ = (M : Set (MacroEdge n)).ncard :=
      Set.ncard_image_of_injective _ macroSegment_injective
    _ = M.card := Set.ncard_coe_finset M

/-- `M` is connected through shared lattice endpoints. -/
def SegmentConnected {n : ℕ} (M : Finset (MacroEdge n)) : Prop :=
  M.Nonempty ∧ ((segmentGraph M).induce (segmentGraph M).support).Connected

abbrev ConnectedSegmentSet (n m : ℕ) :=
  {M : Finset (MacroEdge n) // M.card = m ∧ SegmentConnected M}

noncomputable instance (n m : ℕ) : Fintype (ConnectedSegmentSet n m) :=
  Fintype.ofFinite _

inductive GridDir
  | east | west | north | south
  deriving DecidableEq

def gridDirEquivFin : GridDir ≃ Fin 4 where
  toFun
    | .east => 0
    | .west => 1
    | .north => 2
    | .south => 3
  invFun
    | ⟨0, _⟩ => .east
    | ⟨1, _⟩ => .west
    | ⟨2, _⟩ => .north
    | ⟨3, _⟩ => .south
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

instance : Fintype GridDir := Fintype.ofEquiv (Fin 4) gridDirEquivFin.symm

@[simp] theorem card_gridDir : Fintype.card GridDir = 4 :=
  Fintype.card_congr gridDirEquivFin

def Cell.step (v : Cell) (d : GridDir) : Cell :=
  match d with
  | .east => (v.1 + 1, v.2)
  | .west => (v.1 - 1, v.2)
  | .north => (v.1, v.2 + 1)
  | .south => (v.1, v.2 - 1)

def GridVertex.toCell {n : ℕ} (v : GridVertex n) : Cell :=
  ((v.1.1 : ℤ), (v.2.1 : ℤ))

theorem gridVertex_toCell_injective {n : ℕ} :
    Function.Injective (@GridVertex.toCell n) := by
  intro a b h
  apply Prod.ext <;> apply Fin.ext
  · have h' := congrArg Prod.fst h
    change (a.1.1 : ℤ) = (b.1.1 : ℤ) at h'
    exact_mod_cast h'
  · have h' := congrArg Prod.snd h
    change (a.2.1 : ℤ) = (b.2.1 : ℤ) at h'
    exact_mod_cast h'

private theorem macroSegment_endpoint_bounded {n : ℕ} (e : MacroEdge n)
    {v : Cell} (hv : v ∈ macroSegment e) :
    ∃ q : GridVertex n, q.toCell = v := by
  rcases e with e | e <;>
    simp only [macroSegment, Sym2.mem_iff] at hv <;>
    rcases hv with rfl | rfl
  · exact ⟨(⟨e.1.1 + 1, by omega⟩, ⟨e.2.1, by omega⟩), rfl⟩
  · exact ⟨(⟨e.1.1 + 1, by omega⟩, ⟨e.2.1 + 1, by omega⟩), rfl⟩
  · exact ⟨(⟨e.1.1, by omega⟩, ⟨e.2.1 + 1, by omega⟩), rfl⟩
  · exact ⟨(⟨e.1.1 + 1, by omega⟩, ⟨e.2.1 + 1, by omega⟩), rfl⟩

private theorem segmentGraph_support_bounded {n : ℕ} (M : Finset (MacroEdge n)) :
    (segmentGraph M).support ⊆ Set.range (@GridVertex.toCell n) := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  have he : s(v, w) ∈ (segmentGraph M).edgeSet := hvw
  rw [segmentGraph_edgeSet] at he
  rcases he with ⟨e, -, hseg⟩
  have hvseg : v ∈ macroSegment e := by
    rw [hseg]
    simp
  exact macroSegment_endpoint_bounded e hvseg

private theorem segmentGraph_support_finite {n : ℕ} (M : Finset (MacroEdge n)) :
    (segmentGraph M).support.Finite := by
  exact (Set.finite_range GridVertex.toCell).subset (segmentGraph_support_bounded M)

theorem segmentGraph_adj_has_dir {n : ℕ} {M : Finset (MacroEdge n)}
    {a b : Cell} (h : (segmentGraph M).Adj a b) :
    ∃ d : GridDir, b = a.step d := by
  have he : s(a, b) ∈ (segmentGraph M).edgeSet := h
  rw [segmentGraph_edgeSet] at he
  rcases he with ⟨e, -, hseg⟩
  rcases e with e | e
  · let p₀ : Cell := (((e.1.1 + 1 : ℕ) : ℤ), (e.2.1 : ℤ))
    let p₁ : Cell := (((e.1.1 + 1 : ℕ) : ℤ), ((e.2.1 + 1 : ℕ) : ℤ))
    have hr : (p₀ = a ∧ p₁ = b) ∨ (p₀ = b ∧ p₁ = a) := by
      exact Sym2.rel_iff.mp (Sym2.exact (by simpa [macroSegment, p₀, p₁] using hseg))
    obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := hr
    · refine ⟨.north, ?_⟩
      rw [← ha, ← hb]
      simp [Cell.step, p₀, p₁]
    · refine ⟨.south, ?_⟩
      rw [← ha, ← hb]
      simp [Cell.step, p₀, p₁]
  · let p₀ : Cell := ((e.1.1 : ℤ), ((e.2.1 + 1 : ℕ) : ℤ))
    let p₁ : Cell := (((e.1.1 + 1 : ℕ) : ℤ), ((e.2.1 + 1 : ℕ) : ℤ))
    have hr : (p₀ = a ∧ p₁ = b) ∨ (p₀ = b ∧ p₁ = a) := by
      exact Sym2.rel_iff.mp (Sym2.exact (by simpa [macroSegment, p₀, p₁] using hseg))
    obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := hr
    · refine ⟨.east, ?_⟩
      rw [← ha, ← hb]
      simp [Cell.step, p₀, p₁]
    · refine ⟨.west, ?_⟩
      rw [← ha, ← hb]
      simp [Cell.step, p₀, p₁]

noncomputable def gridDirOfAdj {n : ℕ} {M : Finset (MacroEdge n)}
    {a b : Cell} (h : (segmentGraph M).Adj a b) : GridDir :=
  Classical.choose (segmentGraph_adj_has_dir h)

theorem step_gridDirOfAdj {n : ℕ} {M : Finset (MacroEdge n)}
    {a b : Cell} (h : (segmentGraph M).Adj a b) :
    b = a.step (gridDirOfAdj h) :=
  Classical.choose_spec (segmentGraph_adj_has_dir h)

def walkGridDirs {n : ℕ} {M : Finset (MacroEdge n)} {a b : Cell} :
    (segmentGraph M).Walk a b → List GridDir
  | .nil => []
  | .cons h p => gridDirOfAdj h :: walkGridDirs p

@[simp] theorem length_walkGridDirs {n : ℕ} {M : Finset (MacroEdge n)}
    {a b : Cell} (p : (segmentGraph M).Walk a b) :
    (walkGridDirs p).length = p.length := by
  induction p <;> simp [walkGridDirs, *]

def traceSegments (a : Cell) : List GridDir → Set (Sym2 Cell)
  | [] => ∅
  | d :: ds => insert s(a, a.step d) (traceSegments (a.step d) ds)

theorem traceSegments_walkGridDirs {n : ℕ} {M : Finset (MacroEdge n)}
    {a b : Cell} (p : (segmentGraph M).Walk a b) :
    traceSegments a (walkGridDirs p) = p.edgeSet := by
  induction p with
  | nil => simp [traceSegments, walkGridDirs]
  | @cons a b c h p ih =>
      simp only [walkGridDirs, traceSegments, SimpleGraph.Walk.edgeSet_cons]
      rw [← step_gridDirOfAdj h, ih]

abbrev ConnectedSegmentCode (n m : ℕ) :=
  GridVertex n × List.Vector GridDir (2 * m)

def decodeConnectedSegmentCode {n m : ℕ} (c : ConnectedSegmentCode n m) :
    Set (Sym2 Cell) :=
  traceSegments c.1.toCell c.2.toList

set_option maxHeartbeats 1000000 in
private theorem connectedSegmentCode_exists {n m : ℕ}
    (M : ConnectedSegmentSet n m) :
    ∃ c : ConnectedSegmentCode n m,
      decodeConnectedSegmentCode c = (segmentGraph M.1).edgeSet := by
  classical
  let G : SimpleGraph Cell := segmentGraph M.1
  let S : Set Cell := G.support
  let G' : SimpleGraph S := G.induce S
  letI : Fintype S := (segmentGraph_support_finite M.1).fintype
  have hGedgeFinite : G.edgeSet.Finite := by
    rw [show G.edgeSet = macroSegment '' (M.1 : Set (MacroEdge n)) by
      simpa [G] using segmentGraph_edgeSet M.1]
    exact M.1.finite_toSet.image macroSegment
  letI : Fintype G.edgeSet := hGedgeFinite.fintype
  have hconn : G'.Connected := M.2.2.2
  obtain ⟨r, p, hplen, hpedge⟩ := connected_has_double_edge_cover G' hconn
  let incl : G' →g G := ⟨Subtype.val, fun h => h⟩
  let q : G.Walk r.1 r.1 := p.map incl
  have hqedge : q.edgeSet = G.edgeSet := by
    have hmap : q.edgeSet = G'.spanningCoe.edgeSet := by
      simp only [q, SimpleGraph.Walk.edgeSet_map, hpedge]
      exact (SimpleGraph.edgeSet_map
        (Function.Embedding.subtype (fun z => z ∈ S)) G').symm
    rw [hmap]
    exact congrArg SimpleGraph.edgeSet (G.spanningCoe_induce_support)
  have hq_len : q.length = 2 * m := by
    rw [SimpleGraph.Walk.length_map, hplen]
    have himage : q.edgeSet = Sym2.map incl '' G'.edgeSet := by
      simp only [q, SimpleGraph.Walk.edgeSet_map, hpedge]
    have hincl : Function.Injective incl := by
      intro a b h
      exact Subtype.ext h
    have hcardInd : Nat.card G'.edgeSet = Nat.card G.edgeSet := by
      calc
        Nat.card G'.edgeSet = G'.edgeSet.ncard := rfl
        _ = (Sym2.map incl '' G'.edgeSet).ncard :=
          (Set.ncard_image_of_injective _
            (Sym2.map.injective hincl)).symm
        _ = q.edgeSet.ncard := congrArg Set.ncard himage.symm
        _ = G.edgeSet.ncard := congrArg Set.ncard hqedge
        _ = Nat.card G.edgeSet := rfl
    have hGcard := segmentGraph_edge_card M.1
    change Nat.card G.edgeSet = M.1.card at hGcard
    rw [hcardInd, hGcard, M.2.1]
  have hrange : r.1 ∈ Set.range (@GridVertex.toCell n) := by
    apply segmentGraph_support_bounded M.1
    exact r.2
  obtain ⟨root, hroot⟩ := hrange
  let dirs : List.Vector GridDir (2 * m) :=
    ⟨walkGridDirs q, by simpa [hq_len] using length_walkGridDirs q⟩
  refine ⟨(root, dirs), ?_⟩
  unfold decodeConnectedSegmentCode dirs
  dsimp only
  rw [hroot]
  exact (traceSegments_walkGridDirs q).trans hqedge

noncomputable def encodeConnectedSegment {n m : ℕ}
    (M : ConnectedSegmentSet n m) : ConnectedSegmentCode n m :=
  Classical.choose (connectedSegmentCode_exists M)

theorem encodeConnectedSegment_spec {n m : ℕ}
    (M : ConnectedSegmentSet n m) :
    decodeConnectedSegmentCode (encodeConnectedSegment M) =
      (segmentGraph M.1).edgeSet :=
  Classical.choose_spec (connectedSegmentCode_exists M)

theorem encodeConnectedSegment_injective {n m : ℕ} :
    Function.Injective (@encodeConnectedSegment n m) := by
  intro A B h
  apply Subtype.ext
  apply Finset.coe_injective
  have hg : (segmentGraph A.1).edgeSet = (segmentGraph B.1).edgeSet := by
    rw [← encodeConnectedSegment_spec A, ← encodeConnectedSegment_spec B, h]
  rw [segmentGraph_edgeSet, segmentGraph_edgeSet] at hg
  exact Set.image_injective.mpr macroSegment_injective hg

/-- The Euler-word bound for connected unit-segment sets. -/
theorem card_connectedSegmentSet_le (n m : ℕ) :
    Fintype.card (ConnectedSegmentSet n m) ≤ (n + 1) ^ 2 * 16 ^ m := by
  classical
  calc
    Fintype.card (ConnectedSegmentSet n m) ≤
        Fintype.card (ConnectedSegmentCode n m) :=
      Fintype.card_le_of_injective encodeConnectedSegment encodeConnectedSegment_injective
    _ = (n + 1) ^ 2 * 16 ^ m := by
      simp only [ConnectedSegmentCode, Fintype.card_prod, Fintype.card_fin,
        card_vector, card_gridDir]
      rw [pow_mul]
      ring

/-! ## Components of a set of seam segments -/

def SegmentsTouch {n : ℕ} (e f : MacroEdge n) : Prop :=
  ∃ v : Cell, v ∈ macroSegment e ∧ v ∈ macroSegment f

theorem segmentsTouch_symm {n : ℕ} {e f : MacroEdge n} :
    SegmentsTouch e f → SegmentsTouch f e := by
  rintro ⟨v, he, hf⟩
  exact ⟨v, hf, he⟩

def segmentTouchGraph {n : ℕ} (M : Finset (MacroEdge n)) :
    SimpleGraph ↑M where
  Adj e f := e ≠ f ∧ SegmentsTouch e.1 f.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, segmentsTouch_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem sym2_eq_of_mem_of_mem_of_ne {a b : Cell} (e : Sym2 Cell)
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) : e = s(a, b) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Sym2.mem_iff] at ha hb
      rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
      · exact (hab rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hab rfl).elim

private theorem segmentGraph_support_has_edge {n : ℕ} (M : Finset (MacroEdge n))
    {v : Cell} (hv : v ∈ (segmentGraph M).support) :
    ∃ e ∈ M, v ∈ macroSegment e := by
  rcases hv with ⟨w, hvw⟩
  have he : s(v, w) ∈ (segmentGraph M).edgeSet := hvw
  rw [segmentGraph_edgeSet] at he
  rcases he with ⟨e, heM, hseg⟩
  refine ⟨e, heM, ?_⟩
  rw [hseg]
  simp

private theorem endpoints_reachable {n : ℕ} {M : Finset (MacroEdge n)}
    {e : MacroEdge n} (he : e ∈ M) {a b : Cell}
    (ha : a ∈ macroSegment e) (hb : b ∈ macroSegment e) :
    (segmentGraph M).Reachable a b := by
  by_cases hab : a = b
  · simpa [hab]
  · apply SimpleGraph.Adj.reachable
    rw [segmentGraph, SimpleGraph.fromEdgeSet_adj]
    constructor
    · refine ⟨e, he, ?_⟩
      exact sym2_eq_of_mem_of_mem_of_ne _ ha hb hab
    · exact hab

private theorem touchWalk_endpoints_reachable {n : ℕ} {M : Finset (MacroEdge n)}
    {e f : ↑M} (p : (segmentTouchGraph M).Walk e f)
    {a b : Cell} (ha : a ∈ macroSegment e.1) (hb : b ∈ macroSegment f.1) :
    (segmentGraph M).Reachable a b := by
  induction p generalizing a with
  | @nil e => exact endpoints_reachable e.2 ha hb
  | @cons e g f heg p ih =>
      rcases heg.2 with ⟨v, hev, hgv⟩
      exact (endpoints_reachable e.2 ha hev).trans (ih hgv hb)

private theorem walk_support_subset_graph_support {V : Type} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (ha : a ∈ G.support) :
    ∀ x ∈ p.support, x ∈ G.support := by
  induction p with
  | nil => simpa using ha
  | @cons a b c hab p ih =>
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨b, hab⟩
      · exact ih ⟨a, hab.symm⟩ x hx

theorem segmentConnected_of_touch_connected {n : ℕ} (M : Finset (MacroEdge n))
    (hne : M.Nonempty) (hconn : (segmentTouchGraph M).Connected) :
    SegmentConnected M := by
  refine ⟨hne, ?_⟩
  rw [SimpleGraph.connected_iff]
  constructor
  · intro a b
    rcases segmentGraph_support_has_edge M a.2 with ⟨e, heM, hae⟩
    rcases segmentGraph_support_has_edge M b.2 with ⟨f, hfM, hbf⟩
    let e' : ↑M := ⟨e, heM⟩
    let f' : ↑M := ⟨f, hfM⟩
    obtain ⟨p, -⟩ := hconn.exists_isPath e' f'
    let q := (touchWalk_endpoints_reachable p hae hbf).some
    have hsub : ∀ x ∈ q.support, x ∈ (segmentGraph M).support :=
      walk_support_subset_graph_support q a.2
    exact ⟨(q.induce (segmentGraph M).support hsub).copy
      (SetCoe.ext rfl) (SetCoe.ext rfl)⟩
  · rcases hne with ⟨e, he⟩
    rcases e with e | e
    · let v : Cell := (((e.1.1 + 1 : ℕ) : ℤ), (e.2.1 : ℤ))
      let w : Cell := (((e.1.1 + 1 : ℕ) : ℤ), ((e.2.1 + 1 : ℕ) : ℤ))
      refine ⟨⟨v, ?_⟩⟩
      change ∃ w, (segmentGraph M).Adj v w
      exact ⟨w, by
        rw [segmentGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨Sum.inl e, he, rfl⟩, by simp [v, w]⟩⟩
    · let v : Cell := ((e.1.1 : ℤ), ((e.2.1 + 1 : ℕ) : ℤ))
      let w : Cell := (((e.1.1 + 1 : ℕ) : ℤ), ((e.2.1 + 1 : ℕ) : ℤ))
      refine ⟨⟨v, ?_⟩⟩
      change ∃ w, (segmentGraph M).Adj v w
      exact ⟨w, by
        rw [segmentGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨Sum.inr e, he, rfl⟩, by simp [v, w]⟩⟩

noncomputable def touchComponentEdges {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) : Finset (MacroEdge n) := by
  classical
  letI : Fintype c.supp := Fintype.ofFinite _
  exact c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_touchComponentEdges {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) (e : MacroEdge n) :
    e ∈ touchComponentEdges M c ↔
      ∃ he : e ∈ M, (⟨e, he⟩ : ↑M) ∈ c.supp := by
  classical
  unfold touchComponentEdges
  simp only [Finset.mem_map, Set.mem_toFinset]
  constructor
  · rintro ⟨x, hxc, hx⟩
    subst e
    exact ⟨x.2, hxc⟩
  · rintro ⟨heM, hec⟩
    exact ⟨⟨e, heM⟩, hec, rfl⟩

theorem touchComponentEdges_subset {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) :
    touchComponentEdges M c ⊆ M := by
  intro e he
  rcases (mem_touchComponentEdges M c e).mp he with ⟨heM, -⟩
  exact heM

theorem touchComponentEdges_nonempty {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) :
    (touchComponentEdges M c).Nonempty := by
  rcases c.nonempty_supp with ⟨e, hec⟩
  exact ⟨e.1, (mem_touchComponentEdges M c e.1).mpr ⟨e.2, hec⟩⟩

def touchComponentEdgeEquiv {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) :
    ↑(touchComponentEdges M c) ≃ c.supp where
  toFun e :=
    ⟨⟨e.1, touchComponentEdges_subset M c e.2⟩,
      (mem_touchComponentEdges M c e.1).mp e.2 |>.choose_spec⟩
  invFun e := ⟨e.1.1, (mem_touchComponentEdges M c e.1.1).mpr ⟨e.1.2, e.2⟩⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext (Subtype.ext rfl)

def touchComponentEdgeIso {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) :
    segmentTouchGraph (touchComponentEdges M c) ≃g c.toSimpleGraph where
  toEquiv := touchComponentEdgeEquiv M c
  map_rel_iff' := by
    intro e f
    change ((⟨e.1, touchComponentEdges_subset M c e.2⟩ : ↑M) ≠
        ⟨f.1, touchComponentEdges_subset M c f.2⟩ ∧
        SegmentsTouch e.1 f.1) ↔ (e ≠ f ∧ SegmentsTouch e.1 f.1)
    constructor
    · intro h
      refine ⟨?_, h.2⟩
      intro hef
      apply h.1
      subst f
      rfl
    · intro h
      refine ⟨?_, h.2⟩
      intro hef
      apply h.1
      apply Subtype.ext
      exact congrArg (fun x : ↑M => x.1) hef

theorem touchComponentEdges_touch_connected {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) :
    (segmentTouchGraph (touchComponentEdges M c)).Connected := by
  rw [(touchComponentEdgeIso M c).connected_iff]
  exact c.connected_toSimpleGraph

theorem touchComponentEdges_segmentConnected {n : ℕ} (M : Finset (MacroEdge n))
    (c : (segmentTouchGraph M).ConnectedComponent) :
    SegmentConnected (touchComponentEdges M c) :=
  segmentConnected_of_touch_connected _ (touchComponentEdges_nonempty M c)
    (touchComponentEdges_touch_connected M c)

private theorem verticalSide_reachable_from_start {n : ℕ}
    (M : Finset (MacroEdge n)) (x : Fin (n - 1)) (y₀ len : ℕ)
    (hlen : 0 < len) (hybound : y₀ + len ≤ n)
    (hmem : ∀ k (hk : k < len),
      RectangularPartition.horizontalMacroEdge (n := n) x ⟨y₀ + k, by omega⟩ ∈ M)
    (k : ℕ) (hk : k < len) :
    (segmentTouchGraph M).Reachable
      ⟨RectangularPartition.horizontalMacroEdge (n := n) x ⟨y₀, by omega⟩, hmem 0 hlen⟩
      ⟨RectangularPartition.horizontalMacroEdge (n := n) x ⟨y₀ + k, by omega⟩, hmem k hk⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkprev : k < len := by omega
      have hr := ih hkprev
      let yp : Fin n := ⟨y₀ + k, by omega⟩
      let yn : Fin n := ⟨y₀ + k + 1, by omega⟩
      let ep : MacroEdge n := RectangularPartition.horizontalMacroEdge (n := n) x yp
      let en : MacroEdge n := RectangularPartition.horizontalMacroEdge (n := n) x yn
      have hep : ep ∈ M := hmem k hkprev
      have hen : en ∈ M := hmem (k + 1) hk
      apply hr.trans
      apply SimpleGraph.Adj.reachable
      change (segmentTouchGraph M).Adj ⟨ep, hep⟩ ⟨en, hen⟩
      constructor
      · intro heq
        have hv : ep = en := congrArg (fun e : ↑M => e.1) heq
        have hyv : yp.1 = yn.1 := by
          simp only [ep, en, RectangularPartition.horizontalMacroEdge,
            Sum.inl.injEq, Prod.mk.injEq] at hv
          exact congrArg Fin.val hv.2
        dsimp [yp, yn] at hyv
        omega
      · let v : Cell := (((x.1 + 1 : ℕ) : ℤ), ((y₀ + k + 1 : ℕ) : ℤ))
        refine ⟨v, ?_, ?_⟩ <;>
          simp [ep, en, yp, yn, macroSegment,
            RectangularPartition.horizontalMacroEdge, v, Sym2.mem_iff]

private theorem horizontalSide_reachable_from_start {n : ℕ}
    (M : Finset (MacroEdge n)) (y : Fin (n - 1)) (x₀ len : ℕ)
    (hlen : 0 < len) (hxbound : x₀ + len ≤ n)
    (hmem : ∀ k (hk : k < len),
      RectangularPartition.verticalMacroEdge (n := n) ⟨x₀ + k, by omega⟩ y ∈ M)
    (k : ℕ) (hk : k < len) :
    (segmentTouchGraph M).Reachable
      ⟨RectangularPartition.verticalMacroEdge (n := n) ⟨x₀, by omega⟩ y, hmem 0 hlen⟩
      ⟨RectangularPartition.verticalMacroEdge (n := n) ⟨x₀ + k, by omega⟩ y, hmem k hk⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkprev : k < len := by omega
      have hr := ih hkprev
      let xp : Fin n := ⟨x₀ + k, by omega⟩
      let xn : Fin n := ⟨x₀ + k + 1, by omega⟩
      let ep : MacroEdge n := RectangularPartition.verticalMacroEdge (n := n) xp y
      let en : MacroEdge n := RectangularPartition.verticalMacroEdge (n := n) xn y
      have hep : ep ∈ M := hmem k hkprev
      have hen : en ∈ M := hmem (k + 1) hk
      apply hr.trans
      apply SimpleGraph.Adj.reachable
      change (segmentTouchGraph M).Adj ⟨ep, hep⟩ ⟨en, hen⟩
      constructor
      · intro heq
        have hv : ep = en := congrArg (fun e : ↑M => e.1) heq
        have hxv : xp.1 = xn.1 := by
          simp only [ep, en, RectangularPartition.verticalMacroEdge,
            Sum.inr.injEq, Prod.mk.injEq] at hv
          exact congrArg Fin.val hv.1
        dsimp [xp, xn] at hxv
        omega
      · let v : Cell := (((x₀ + k + 1 : ℕ) : ℤ), ((y.1 + 1 : ℕ) : ℤ))
        refine ⟨v, ?_, ?_⟩ <;>
          simp [ep, en, xp, xn, macroSegment,
            RectangularPartition.verticalMacroEdge, v, Sym2.mem_iff]

private inductive RectSide
  | west | east | south | north
  deriving DecidableEq

private def rectSideEquivFin : RectSide ≃ Fin 4 where
  toFun
    | .west => 0
    | .east => 1
    | .south => 2
    | .north => 3
  invFun
    | ⟨0, _⟩ => .west
    | ⟨1, _⟩ => .east
    | ⟨2, _⟩ => .south
    | ⟨3, _⟩ => .north
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

private instance : Fintype RectSide := Fintype.ofEquiv (Fin 4) rectSideEquivFin.symm

private def GridRectangle.sideInternal {n : ℕ} (B : GridRectangle n) :
    RectSide → Prop
  | .west => 0 < B.x₀.1
  | .east => B.x₀.1 + B.width.1 < n
  | .south => 0 < B.y₀.1
  | .north => B.y₀.1 + B.height.1 < n

private def GridRectangle.sideLen {n : ℕ} (B : GridRectangle n) :
    RectSide → ℕ
  | .west | .east => B.height.1
  | .south | .north => B.width.1

private def GridRectangle.EdgeOnSide {n : ℕ} (B : GridRectangle n)
    (s : RectSide) (e : MacroEdge n) : Prop :=
  match s, e with
  | .west, .inl e => e.1.1 + 1 = B.x₀.1 ∧
      B.y₀.1 ≤ e.2.1 ∧ e.2.1 < B.y₀.1 + B.height.1
  | .east, .inl e => e.1.1 + 1 = B.x₀.1 + B.width.1 ∧
      B.y₀.1 ≤ e.2.1 ∧ e.2.1 < B.y₀.1 + B.height.1
  | .south, .inr e => e.2.1 + 1 = B.y₀.1 ∧
      B.x₀.1 ≤ e.1.1 ∧ e.1.1 < B.x₀.1 + B.width.1
  | .north, .inr e => e.2.1 + 1 = B.y₀.1 + B.height.1 ∧
      B.x₀.1 ≤ e.1.1 ∧ e.1.1 < B.x₀.1 + B.width.1
  | _, _ => False

private theorem incident_seam_has_internal_side {n : ℕ}
    (D : RectangularPartition n) (B : ↑D.blocks) {e : MacroEdge n}
    (he : e ∈ D.seamEdges)
    (hinc : B.1.Contains e.lo ∨ B.1.Contains e.hi) :
    ∃ s : RectSide, B.1.sideInternal s ∧ B.1.EdgeOnSide s e := by
  have hnotopen : ¬ D.SameBlock e.lo e.hi := by
    change ¬ D.IsOpen e
    simpa [RectangularPartition.seamEdges] using he
  have hnotboth : ¬ (B.1.Contains e.lo ∧ B.1.Contains e.hi) := by
    rintro ⟨hlo, hhi⟩
    exact hnotopen ⟨B.1, B.2, hlo, hhi⟩
  rcases e with e | e
  · rcases hinc with hlo | hhi
    · have hnhi : ¬ B.1.Contains (MacroEdge.hi (Sum.inl e : MacroEdge n)) :=
        fun h => hnotboth ⟨hlo, h⟩
      refine ⟨.east, ?_, ?_⟩
      · unfold GridRectangle.sideInternal
        unfold GridRectangle.Contains at hlo hnhi
        dsimp [MacroEdge.lo, MacroEdge.hi] at hlo hnhi
        omega
      · unfold GridRectangle.EdgeOnSide
        unfold GridRectangle.Contains at hlo hnhi
        dsimp [MacroEdge.lo, MacroEdge.hi] at hlo hnhi
        omega
    · have hnlo : ¬ B.1.Contains (MacroEdge.lo (Sum.inl e : MacroEdge n)) :=
        fun h => hnotboth ⟨h, hhi⟩
      refine ⟨.west, ?_, ?_⟩
      · unfold GridRectangle.sideInternal
        unfold GridRectangle.Contains at hhi hnlo
        dsimp [MacroEdge.lo, MacroEdge.hi] at hhi hnlo
        omega
      · unfold GridRectangle.EdgeOnSide
        unfold GridRectangle.Contains at hhi hnlo
        dsimp [MacroEdge.lo, MacroEdge.hi] at hhi hnlo
        omega
  · rcases hinc with hlo | hhi
    · have hnhi : ¬ B.1.Contains (MacroEdge.hi (Sum.inr e : MacroEdge n)) :=
        fun h => hnotboth ⟨hlo, h⟩
      refine ⟨.north, ?_, ?_⟩
      · unfold GridRectangle.sideInternal
        unfold GridRectangle.Contains at hlo hnhi
        dsimp [MacroEdge.lo, MacroEdge.hi] at hlo hnhi
        omega
      · unfold GridRectangle.EdgeOnSide
        unfold GridRectangle.Contains at hlo hnhi
        dsimp [MacroEdge.lo, MacroEdge.hi] at hlo hnhi
        omega
    · have hnlo : ¬ B.1.Contains (MacroEdge.lo (Sum.inr e : MacroEdge n)) :=
        fun h => hnotboth ⟨h, hhi⟩
      refine ⟨.south, ?_, ?_⟩
      · unfold GridRectangle.sideInternal
        unfold GridRectangle.Contains at hhi hnlo
        dsimp [MacroEdge.lo, MacroEdge.hi] at hhi hnlo
        omega
      · unfold GridRectangle.EdgeOnSide
        unfold GridRectangle.Contains at hhi hnlo
        dsimp [MacroEdge.lo, MacroEdge.hi] at hhi hnlo
        omega

private theorem edge_mem_seam_of_block_separates {n : ℕ}
    (D : RectangularPartition n) (B : ↑D.blocks) (e : MacroEdge n)
    (hsep : (B.1.Contains e.lo ∧ ¬ B.1.Contains e.hi) ∨
      (B.1.Contains e.hi ∧ ¬ B.1.Contains e.lo)) :
    e ∈ D.seamEdges := by
  rw [RectangularPartition.mem_seamEdges]
  intro hopen
  rcases hopen with ⟨C, hC, hlo, hhi⟩
  rcases hsep with ⟨hBlo, hBnhi⟩ | ⟨hBhi, hBnlo⟩
  · have hBC := (D.unique_block e.lo).unique ⟨B.2, hBlo⟩ ⟨hC, hlo⟩
    subst C
    exact hBnhi hhi
  · have hBC := (D.unique_block e.hi).unique ⟨B.2, hBhi⟩ ⟨hC, hhi⟩
    subst C
    exact hBnlo hlo

private def westSideEdge {n : ℕ} (B : GridRectangle n)
    (hw : B.sideInternal .west) (k : Fin B.height.1) : MacroEdge n :=
  RectangularPartition.horizontalMacroEdge
    ⟨B.x₀.1 - 1, by unfold GridRectangle.sideInternal at hw; omega⟩
    ⟨B.y₀.1 + k.1, by have := B.y_bound; omega⟩

private def eastSideEdge {n : ℕ} (B : GridRectangle n)
    (he : B.sideInternal .east) (k : Fin B.height.1) : MacroEdge n :=
  RectangularPartition.horizontalMacroEdge
    ⟨B.x₀.1 + B.width.1 - 1,
      by
        unfold GridRectangle.sideInternal at he
        have := B.width_pos
        omega⟩
    ⟨B.y₀.1 + k.1, by have := B.y_bound; omega⟩

private def southSideEdge {n : ℕ} (B : GridRectangle n)
    (hs : B.sideInternal .south) (k : Fin B.width.1) : MacroEdge n :=
  RectangularPartition.verticalMacroEdge
    ⟨B.x₀.1 + k.1, by have := B.x_bound; omega⟩
    ⟨B.y₀.1 - 1, by unfold GridRectangle.sideInternal at hs; omega⟩

private def northSideEdge {n : ℕ} (B : GridRectangle n)
    (hn : B.sideInternal .north) (k : Fin B.width.1) : MacroEdge n :=
  RectangularPartition.verticalMacroEdge
    ⟨B.x₀.1 + k.1, by have := B.x_bound; omega⟩
    ⟨B.y₀.1 + B.height.1 - 1,
      by
        unfold GridRectangle.sideInternal at hn
        have := B.height_pos
        omega⟩

private theorem westSideEdge_mem_seam {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hw : B.1.sideInternal .west) (k : Fin B.1.height.1) :
    westSideEdge B.1 hw k ∈ D.seamEdges := by
  apply edge_mem_seam_of_block_separates D B
  right
  constructor
  · dsimp [westSideEdge, RectangularPartition.horizontalMacroEdge, MacroEdge.hi]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    have := B.1.width_pos
    have := B.1.y_bound
    have := B.1.x₀.2
    unfold GridRectangle.sideInternal at hw
    omega
  · dsimp [westSideEdge, RectangularPartition.horizontalMacroEdge, MacroEdge.lo]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    unfold GridRectangle.sideInternal at hw
    omega

private theorem eastSideEdge_mem_seam {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (he : B.1.sideInternal .east) (k : Fin B.1.height.1) :
    eastSideEdge B.1 he k ∈ D.seamEdges := by
  apply edge_mem_seam_of_block_separates D B
  left
  constructor
  · dsimp [eastSideEdge, RectangularPartition.horizontalMacroEdge, MacroEdge.lo]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    have := B.1.width_pos
    omega
  · dsimp [eastSideEdge, RectangularPartition.horizontalMacroEdge, MacroEdge.hi]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    omega

private theorem southSideEdge_mem_seam {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hs : B.1.sideInternal .south) (k : Fin B.1.width.1) :
    southSideEdge B.1 hs k ∈ D.seamEdges := by
  apply edge_mem_seam_of_block_separates D B
  right
  constructor
  · dsimp [southSideEdge, RectangularPartition.verticalMacroEdge, MacroEdge.hi]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    have := B.1.height_pos
    have := B.1.x_bound
    have := B.1.y₀.2
    unfold GridRectangle.sideInternal at hs
    omega
  · dsimp [southSideEdge, RectangularPartition.verticalMacroEdge, MacroEdge.lo]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    unfold GridRectangle.sideInternal at hs
    omega

private theorem northSideEdge_mem_seam {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hn : B.1.sideInternal .north) (k : Fin B.1.width.1) :
    northSideEdge B.1 hn k ∈ D.seamEdges := by
  apply edge_mem_seam_of_block_separates D B
  left
  constructor
  · dsimp [northSideEdge, RectangularPartition.verticalMacroEdge, MacroEdge.lo]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    have := B.1.height_pos
    omega
  · dsimp [northSideEdge, RectangularPartition.verticalMacroEdge, MacroEdge.hi]
    unfold GridRectangle.Contains
    simp only [Prod.fst, Prod.snd]
    omega

private theorem edgeOnWest_iff {n : ℕ} (B : GridRectangle n)
    (hw : B.sideInternal .west) (e : MacroEdge n) :
    B.EdgeOnSide .west e ↔ ∃ k : Fin B.height.1, e = westSideEdge B hw k := by
  rcases e with e | e
  · unfold GridRectangle.EdgeOnSide
    constructor
    · rintro ⟨hx, hy0, hy1⟩
      let k : Fin B.height.1 := ⟨e.2.1 - B.y₀.1, by omega⟩
      refine ⟨k, ?_⟩
      apply congrArg Sum.inl
      apply Prod.ext <;> apply Fin.ext
      · dsimp [westSideEdge, RectangularPartition.horizontalMacroEdge]
        omega
      · dsimp [westSideEdge, RectangularPartition.horizontalMacroEdge, k]
        omega
    · rintro ⟨k, hk⟩
      rw [hk]
      dsimp [westSideEdge, RectangularPartition.horizontalMacroEdge]
      unfold GridRectangle.sideInternal at hw
      omega
  · constructor
    · intro h
      exact h.elim
    · rintro ⟨k, hk⟩
      simpa [westSideEdge, RectangularPartition.horizontalMacroEdge] using hk

private theorem edgeOnEast_iff {n : ℕ} (B : GridRectangle n)
    (he : B.sideInternal .east) (e : MacroEdge n) :
    B.EdgeOnSide .east e ↔ ∃ k : Fin B.height.1, e = eastSideEdge B he k := by
  rcases e with e | e
  · unfold GridRectangle.EdgeOnSide
    constructor
    · rintro ⟨hx, hy0, hy1⟩
      let k : Fin B.height.1 := ⟨e.2.1 - B.y₀.1, by omega⟩
      refine ⟨k, ?_⟩
      apply congrArg Sum.inl
      apply Prod.ext <;> apply Fin.ext
      · dsimp [eastSideEdge, RectangularPartition.horizontalMacroEdge]
        omega
      · dsimp [eastSideEdge, RectangularPartition.horizontalMacroEdge, k]
        omega
    · rintro ⟨k, hk⟩
      rw [hk]
      dsimp [eastSideEdge, RectangularPartition.horizontalMacroEdge]
      unfold GridRectangle.sideInternal at he
      have := B.height_pos
      have := B.width_pos
      omega
  · constructor
    · intro h
      exact h.elim
    · rintro ⟨k, hk⟩
      simpa [eastSideEdge, RectangularPartition.horizontalMacroEdge] using hk

private theorem edgeOnSouth_iff {n : ℕ} (B : GridRectangle n)
    (hs : B.sideInternal .south) (e : MacroEdge n) :
    B.EdgeOnSide .south e ↔ ∃ k : Fin B.width.1, e = southSideEdge B hs k := by
  rcases e with e | e
  · constructor
    · intro h
      exact h.elim
    · rintro ⟨k, hk⟩
      simpa [southSideEdge, RectangularPartition.verticalMacroEdge] using hk
  · unfold GridRectangle.EdgeOnSide
    constructor
    · rintro ⟨hy, hx0, hx1⟩
      let k : Fin B.width.1 := ⟨e.1.1 - B.x₀.1, by omega⟩
      refine ⟨k, ?_⟩
      apply congrArg Sum.inr
      apply Prod.ext <;> apply Fin.ext
      · dsimp [southSideEdge, RectangularPartition.verticalMacroEdge, k]
        omega
      · dsimp [southSideEdge, RectangularPartition.verticalMacroEdge]
        omega
    · rintro ⟨k, hk⟩
      rw [hk]
      dsimp [southSideEdge, RectangularPartition.verticalMacroEdge]
      unfold GridRectangle.sideInternal at hs
      omega

private theorem edgeOnNorth_iff {n : ℕ} (B : GridRectangle n)
    (hn : B.sideInternal .north) (e : MacroEdge n) :
    B.EdgeOnSide .north e ↔ ∃ k : Fin B.width.1, e = northSideEdge B hn k := by
  rcases e with e | e
  · constructor
    · intro h
      exact h.elim
    · rintro ⟨k, hk⟩
      simpa [northSideEdge, RectangularPartition.verticalMacroEdge] using hk
  · unfold GridRectangle.EdgeOnSide
    constructor
    · rintro ⟨hy, hx0, hx1⟩
      let k : Fin B.width.1 := ⟨e.1.1 - B.x₀.1, by omega⟩
      refine ⟨k, ?_⟩
      apply congrArg Sum.inr
      apply Prod.ext <;> apply Fin.ext
      · dsimp [northSideEdge, RectangularPartition.verticalMacroEdge, k]
        omega
      · dsimp [northSideEdge, RectangularPartition.verticalMacroEdge]
        omega
    · rintro ⟨k, hk⟩
      rw [hk]
      dsimp [northSideEdge, RectangularPartition.verticalMacroEdge]
      unfold GridRectangle.sideInternal at hn
      have := B.width_pos
      have := B.height_pos
      omega

private theorem westSide_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hw : B.1.sideInternal .west)
    (k l : Fin B.1.height.1) :
    (segmentTouchGraph D.seamEdges).Reachable
      ⟨westSideEdge B.1 hw k, westSideEdge_mem_seam D B hw k⟩
      ⟨westSideEdge B.1 hw l, westSideEdge_mem_seam D B hw l⟩ := by
  let bx : Fin (n - 1) := ⟨B.1.x₀.1 - 1, by
    unfold GridRectangle.sideInternal at hw
    omega⟩
  have hbase (t : Fin B.1.height.1) :=
    verticalSide_reachable_from_start D.seamEdges bx B.1.y₀.1 B.1.height.1
      B.1.height_pos B.1.y_bound
      (fun j hj => westSideEdge_mem_seam D B hw ⟨j, hj⟩) t.1 t.2
  exact (by simpa [westSideEdge, bx] using (hbase k).symm.trans (hbase l))

private theorem eastSide_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (he : B.1.sideInternal .east)
    (k l : Fin B.1.height.1) :
    (segmentTouchGraph D.seamEdges).Reachable
      ⟨eastSideEdge B.1 he k, eastSideEdge_mem_seam D B he k⟩
      ⟨eastSideEdge B.1 he l, eastSideEdge_mem_seam D B he l⟩ := by
  let bx : Fin (n - 1) := ⟨B.1.x₀.1 + B.1.width.1 - 1, by
    unfold GridRectangle.sideInternal at he
    have := B.1.width_pos
    omega⟩
  have hbase (t : Fin B.1.height.1) :=
    verticalSide_reachable_from_start D.seamEdges bx B.1.y₀.1 B.1.height.1
      B.1.height_pos B.1.y_bound
      (fun j hj => eastSideEdge_mem_seam D B he ⟨j, hj⟩) t.1 t.2
  exact (by simpa [eastSideEdge, bx] using (hbase k).symm.trans (hbase l))

private theorem southSide_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hs : B.1.sideInternal .south)
    (k l : Fin B.1.width.1) :
    (segmentTouchGraph D.seamEdges).Reachable
      ⟨southSideEdge B.1 hs k, southSideEdge_mem_seam D B hs k⟩
      ⟨southSideEdge B.1 hs l, southSideEdge_mem_seam D B hs l⟩ := by
  let byCoord : Fin (n - 1) := ⟨B.1.y₀.1 - 1, by
    unfold GridRectangle.sideInternal at hs
    omega⟩
  have hbase (t : Fin B.1.width.1) :=
    horizontalSide_reachable_from_start D.seamEdges byCoord B.1.x₀.1 B.1.width.1
      B.1.width_pos B.1.x_bound
      (fun j hj => southSideEdge_mem_seam D B hs ⟨j, hj⟩) t.1 t.2
  exact (by simpa [southSideEdge, byCoord] using (hbase k).symm.trans (hbase l))

private theorem northSide_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hn : B.1.sideInternal .north)
    (k l : Fin B.1.width.1) :
    (segmentTouchGraph D.seamEdges).Reachable
      ⟨northSideEdge B.1 hn k, northSideEdge_mem_seam D B hn k⟩
      ⟨northSideEdge B.1 hn l, northSideEdge_mem_seam D B hn l⟩ := by
  let byCoord : Fin (n - 1) := ⟨B.1.y₀.1 + B.1.height.1 - 1, by
    unfold GridRectangle.sideInternal at hn
    have := B.1.height_pos
    omega⟩
  have hbase (t : Fin B.1.width.1) :=
    horizontalSide_reachable_from_start D.seamEdges byCoord B.1.x₀.1 B.1.width.1
      B.1.width_pos B.1.x_bound
      (fun j hj => northSideEdge_mem_seam D B hn ⟨j, hj⟩) t.1 t.2
  exact (by simpa [northSideEdge, byCoord] using (hbase k).symm.trans (hbase l))

private theorem sideLen_le_component_card {n : ℕ}
    (D : RectangularPartition n)
    (c : (segmentTouchGraph D.seamEdges).ConnectedComponent)
    (B : ↑D.blocks) (s : RectSide) (hs : B.1.sideInternal s)
    {e : MacroEdge n} (he : e ∈ D.seamEdges)
    (hec : (⟨e, he⟩ : ↑D.seamEdges) ∈ c.supp)
    (hes : B.1.EdgeOnSide s e) :
    B.1.sideLen s ≤ (touchComponentEdges D.seamEdges c).card := by
  classical
  cases s
  · obtain ⟨k, hk⟩ := (edgeOnWest_iff B.1 hs e).mp hes
    have hec' : (⟨westSideEdge B.1 hs k, westSideEdge_mem_seam D B hs k⟩ :
        ↑D.seamEdges) ∈ c.supp := by
      simpa [← hk] using hec
    let g : Fin B.1.height.1 → ↑(touchComponentEdges D.seamEdges c) := fun t =>
      ⟨westSideEdge B.1 hs t, (mem_touchComponentEdges D.seamEdges c _).mpr
        ⟨westSideEdge_mem_seam D B hs t,
          (SimpleGraph.ConnectedComponent.sound (westSide_reachable D B hs k t)).symm.trans hec'⟩⟩
    have hg : Function.Injective g := by
      intro a b hab
      have hv := congrArg (fun z : ↑(touchComponentEdges D.seamEdges c) => z.1) hab
      simp only [g, westSideEdge, RectangularPartition.horizontalMacroEdge,
        Sum.inl.injEq, Prod.mk.injEq] at hv
      apply Fin.ext
      exact Nat.add_left_cancel (Fin.ext_iff.mp hv.2)
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc

  · obtain ⟨k, hk⟩ := (edgeOnEast_iff B.1 hs e).mp hes
    have hec' : (⟨eastSideEdge B.1 hs k, eastSideEdge_mem_seam D B hs k⟩ :
        ↑D.seamEdges) ∈ c.supp := by
      simpa [← hk] using hec
    let g : Fin B.1.height.1 → ↑(touchComponentEdges D.seamEdges c) := fun t =>
      ⟨eastSideEdge B.1 hs t, (mem_touchComponentEdges D.seamEdges c _).mpr
        ⟨eastSideEdge_mem_seam D B hs t,
          (SimpleGraph.ConnectedComponent.sound (eastSide_reachable D B hs k t)).symm.trans hec'⟩⟩
    have hg : Function.Injective g := by
      intro a b hab
      have hv := congrArg (fun z : ↑(touchComponentEdges D.seamEdges c) => z.1) hab
      simp only [g, eastSideEdge, RectangularPartition.horizontalMacroEdge,
        Sum.inl.injEq, Prod.mk.injEq] at hv
      apply Fin.ext
      exact Nat.add_left_cancel (Fin.ext_iff.mp hv.2)
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc

  · obtain ⟨k, hk⟩ := (edgeOnSouth_iff B.1 hs e).mp hes
    have hec' : (⟨southSideEdge B.1 hs k, southSideEdge_mem_seam D B hs k⟩ :
        ↑D.seamEdges) ∈ c.supp := by
      simpa [← hk] using hec
    let g : Fin B.1.width.1 → ↑(touchComponentEdges D.seamEdges c) := fun t =>
      ⟨southSideEdge B.1 hs t, (mem_touchComponentEdges D.seamEdges c _).mpr
        ⟨southSideEdge_mem_seam D B hs t,
          (SimpleGraph.ConnectedComponent.sound (southSide_reachable D B hs k t)).symm.trans hec'⟩⟩
    have hg : Function.Injective g := by
      intro a b hab
      have hv := congrArg (fun z : ↑(touchComponentEdges D.seamEdges c) => z.1) hab
      simp only [g, southSideEdge, RectangularPartition.verticalMacroEdge,
        Sum.inr.injEq, Prod.mk.injEq] at hv
      apply Fin.ext
      exact Nat.add_left_cancel (Fin.ext_iff.mp hv.1)
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc

  · obtain ⟨k, hk⟩ := (edgeOnNorth_iff B.1 hs e).mp hes
    have hec' : (⟨northSideEdge B.1 hs k, northSideEdge_mem_seam D B hs k⟩ :
        ↑D.seamEdges) ∈ c.supp := by
      simpa [← hk] using hec
    let g : Fin B.1.width.1 → ↑(touchComponentEdges D.seamEdges c) := fun t =>
      ⟨northSideEdge B.1 hs t, (mem_touchComponentEdges D.seamEdges c _).mpr
        ⟨northSideEdge_mem_seam D B hs t,
          (SimpleGraph.ConnectedComponent.sound (northSide_reachable D B hs k t)).symm.trans hec'⟩⟩
    have hg : Function.Injective g := by
      intro a b hab
      have hv := congrArg (fun z : ↑(touchComponentEdges D.seamEdges c) => z.1) hab
      simp only [g, northSideEdge, RectangularPartition.verticalMacroEdge,
        Sum.inr.injEq, Prod.mk.injEq] at hv
      apply Fin.ext
      exact Nat.add_left_cancel (Fin.ext_iff.mp hv.1)
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc

private theorem same_side_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (s : RectSide) (hs : B.1.sideInternal s)
    {e f : MacroEdge n} (he : e ∈ D.seamEdges) (hf : f ∈ D.seamEdges)
    (hes : B.1.EdgeOnSide s e) (hfs : B.1.EdgeOnSide s f) :
    (segmentTouchGraph D.seamEdges).Reachable ⟨e, he⟩ ⟨f, hf⟩ := by
  cases s
  · obtain ⟨k, hk⟩ := (edgeOnWest_iff B.1 hs e).mp hes
    obtain ⟨l, hl⟩ := (edgeOnWest_iff B.1 hs f).mp hfs
    simpa [hk, hl] using westSide_reachable D B hs k l
  · obtain ⟨k, hk⟩ := (edgeOnEast_iff B.1 hs e).mp hes
    obtain ⟨l, hl⟩ := (edgeOnEast_iff B.1 hs f).mp hfs
    simpa [hk, hl] using eastSide_reachable D B hs k l
  · obtain ⟨k, hk⟩ := (edgeOnSouth_iff B.1 hs e).mp hes
    obtain ⟨l, hl⟩ := (edgeOnSouth_iff B.1 hs f).mp hfs
    simpa [hk, hl] using southSide_reachable D B hs k l
  · obtain ⟨k, hk⟩ := (edgeOnNorth_iff B.1 hs e).mp hes
    obtain ⟨l, hl⟩ := (edgeOnNorth_iff B.1 hs f).mp hfs
    simpa [hk, hl] using northSide_reachable D B hs k l

private theorem westSouth_adj {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hw : B.1.sideInternal .west)
    (hs : B.1.sideInternal .south) :
    (segmentTouchGraph D.seamEdges).Adj
      ⟨westSideEdge B.1 hw ⟨0, B.1.height_pos⟩,
        westSideEdge_mem_seam D B hw ⟨0, B.1.height_pos⟩⟩
      ⟨southSideEdge B.1 hs ⟨0, B.1.width_pos⟩,
        southSideEdge_mem_seam D B hs ⟨0, B.1.width_pos⟩⟩ := by
  unfold GridRectangle.sideInternal at hw hs
  have hx := B.1.x_bound
  have hy := B.1.y_bound
  have hwp := B.1.width_pos
  have hhp := B.1.height_pos
  constructor
  · intro h
    have := congrArg (fun z : ↑D.seamEdges => z.1) h
    simpa [westSideEdge, southSideEdge,
      RectangularPartition.horizontalMacroEdge,
      RectangularPartition.verticalMacroEdge] using this
  · let v : Cell := ((B.1.x₀.1 : ℤ), (B.1.y₀.1 : ℤ))
    refine ⟨v, ?_, ?_⟩ <;>
      simp [westSideEdge, southSideEdge, macroSegment,
        RectangularPartition.horizontalMacroEdge,
        RectangularPartition.verticalMacroEdge, v, Sym2.mem_iff] <;>
      omega

private theorem westNorth_adj {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hw : B.1.sideInternal .west)
    (hn : B.1.sideInternal .north) :
    (segmentTouchGraph D.seamEdges).Adj
      ⟨westSideEdge B.1 hw ⟨B.1.height.1 - 1, by have := B.1.height_pos; omega⟩,
        westSideEdge_mem_seam D B hw _⟩
      ⟨northSideEdge B.1 hn ⟨0, B.1.width_pos⟩,
        northSideEdge_mem_seam D B hn ⟨0, B.1.width_pos⟩⟩ := by
  unfold GridRectangle.sideInternal at hw hn
  have hx := B.1.x_bound
  have hy := B.1.y_bound
  have hwp := B.1.width_pos
  have hhp := B.1.height_pos
  constructor
  · intro h
    have := congrArg (fun z : ↑D.seamEdges => z.1) h
    simpa [westSideEdge, northSideEdge,
      RectangularPartition.horizontalMacroEdge,
      RectangularPartition.verticalMacroEdge] using this
  · let v : Cell := ((B.1.x₀.1 : ℤ), ((B.1.y₀.1 + B.1.height.1 : ℕ) : ℤ))
    refine ⟨v, ?_, ?_⟩ <;>
      simp [westSideEdge, northSideEdge, macroSegment,
        RectangularPartition.horizontalMacroEdge,
        RectangularPartition.verticalMacroEdge, v, Sym2.mem_iff] <;>
      omega

private theorem eastSouth_adj {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (he : B.1.sideInternal .east)
    (hs : B.1.sideInternal .south) :
    (segmentTouchGraph D.seamEdges).Adj
      ⟨eastSideEdge B.1 he ⟨0, B.1.height_pos⟩,
        eastSideEdge_mem_seam D B he ⟨0, B.1.height_pos⟩⟩
      ⟨southSideEdge B.1 hs ⟨B.1.width.1 - 1, by have := B.1.width_pos; omega⟩,
        southSideEdge_mem_seam D B hs _⟩ := by
  unfold GridRectangle.sideInternal at he hs
  have hx := B.1.x_bound
  have hy := B.1.y_bound
  have hwp := B.1.width_pos
  have hhp := B.1.height_pos
  constructor
  · intro h
    have := congrArg (fun z : ↑D.seamEdges => z.1) h
    simpa [eastSideEdge, southSideEdge,
      RectangularPartition.horizontalMacroEdge,
      RectangularPartition.verticalMacroEdge] using this
  · let v : Cell := (((B.1.x₀.1 + B.1.width.1 : ℕ) : ℤ), (B.1.y₀.1 : ℤ))
    refine ⟨v, ?_, ?_⟩ <;>
      simp [eastSideEdge, southSideEdge, macroSegment,
        RectangularPartition.horizontalMacroEdge,
        RectangularPartition.verticalMacroEdge, v, Sym2.mem_iff] <;>
      omega

private theorem eastNorth_adj {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (he : B.1.sideInternal .east)
    (hn : B.1.sideInternal .north) :
    (segmentTouchGraph D.seamEdges).Adj
      ⟨eastSideEdge B.1 he ⟨B.1.height.1 - 1, by have := B.1.height_pos; omega⟩,
        eastSideEdge_mem_seam D B he _⟩
      ⟨northSideEdge B.1 hn ⟨B.1.width.1 - 1, by have := B.1.width_pos; omega⟩,
        northSideEdge_mem_seam D B hn _⟩ := by
  unfold GridRectangle.sideInternal at he hn
  have hx := B.1.x_bound
  have hy := B.1.y_bound
  have hwp := B.1.width_pos
  have hhp := B.1.height_pos
  constructor
  · intro h
    have := congrArg (fun z : ↑D.seamEdges => z.1) h
    simpa [eastSideEdge, northSideEdge,
      RectangularPartition.horizontalMacroEdge,
      RectangularPartition.verticalMacroEdge] using this
  · let v : Cell := (((B.1.x₀.1 + B.1.width.1 : ℕ) : ℤ),
      ((B.1.y₀.1 + B.1.height.1 : ℕ) : ℤ))
    refine ⟨v, ?_, ?_⟩ <;>
      simp [eastSideEdge, northSideEdge, macroSegment,
        RectangularPartition.horizontalMacroEdge,
        RectangularPartition.verticalMacroEdge, v, Sym2.mem_iff] <;>
      omega

private theorem westSouth_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hw : B.1.sideInternal .west)
    (hs : B.1.sideInternal .south)
    {e f : MacroEdge n} (he : e ∈ D.seamEdges) (hf : f ∈ D.seamEdges)
    (hes : B.1.EdgeOnSide .west e) (hfs : B.1.EdgeOnSide .south f) :
    (segmentTouchGraph D.seamEdges).Reachable ⟨e, he⟩ ⟨f, hf⟩ := by
  let kw : Fin B.1.height.1 := ⟨0, B.1.height_pos⟩
  let ks : Fin B.1.width.1 := ⟨0, B.1.width_pos⟩
  have hwc : B.1.EdgeOnSide .west (westSideEdge B.1 hw kw) :=
    (edgeOnWest_iff B.1 hw _).mpr ⟨kw, rfl⟩
  have hsc : B.1.EdgeOnSide .south (southSideEdge B.1 hs ks) :=
    (edgeOnSouth_iff B.1 hs _).mpr ⟨ks, rfl⟩
  exact (same_side_reachable D B .west hw he _ hes hwc).trans
    ((westSouth_adj D B hw hs).reachable.trans
      (same_side_reachable D B .south hs _ hf hsc hfs))

private theorem westNorth_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (hw : B.1.sideInternal .west)
    (hn : B.1.sideInternal .north)
    {e f : MacroEdge n} (he : e ∈ D.seamEdges) (hf : f ∈ D.seamEdges)
    (hes : B.1.EdgeOnSide .west e) (hfs : B.1.EdgeOnSide .north f) :
    (segmentTouchGraph D.seamEdges).Reachable ⟨e, he⟩ ⟨f, hf⟩ := by
  let kw : Fin B.1.height.1 := ⟨B.1.height.1 - 1, by have := B.1.height_pos; omega⟩
  let kn : Fin B.1.width.1 := ⟨0, B.1.width_pos⟩
  have hwc : B.1.EdgeOnSide .west (westSideEdge B.1 hw kw) :=
    (edgeOnWest_iff B.1 hw _).mpr ⟨kw, rfl⟩
  have hnc : B.1.EdgeOnSide .north (northSideEdge B.1 hn kn) :=
    (edgeOnNorth_iff B.1 hn _).mpr ⟨kn, rfl⟩
  exact (same_side_reachable D B .west hw he _ hes hwc).trans
    ((westNorth_adj D B hw hn).reachable.trans
      (same_side_reachable D B .north hn _ hf hnc hfs))

private theorem eastSouth_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (heas : B.1.sideInternal .east)
    (hs : B.1.sideInternal .south)
    {e f : MacroEdge n} (he : e ∈ D.seamEdges) (hf : f ∈ D.seamEdges)
    (hes : B.1.EdgeOnSide .east e) (hfs : B.1.EdgeOnSide .south f) :
    (segmentTouchGraph D.seamEdges).Reachable ⟨e, he⟩ ⟨f, hf⟩ := by
  let ke : Fin B.1.height.1 := ⟨0, B.1.height_pos⟩
  let ks : Fin B.1.width.1 := ⟨B.1.width.1 - 1, by have := B.1.width_pos; omega⟩
  have hec : B.1.EdgeOnSide .east (eastSideEdge B.1 heas ke) :=
    (edgeOnEast_iff B.1 heas _).mpr ⟨ke, rfl⟩
  have hsc : B.1.EdgeOnSide .south (southSideEdge B.1 hs ks) :=
    (edgeOnSouth_iff B.1 hs _).mpr ⟨ks, rfl⟩
  exact (same_side_reachable D B .east heas he _ hes hec).trans
    ((eastSouth_adj D B heas hs).reachable.trans
      (same_side_reachable D B .south hs _ hf hsc hfs))

private theorem eastNorth_reachable {n : ℕ} (D : RectangularPartition n)
    (B : ↑D.blocks) (heas : B.1.sideInternal .east)
    (hn : B.1.sideInternal .north)
    {e f : MacroEdge n} (he : e ∈ D.seamEdges) (hf : f ∈ D.seamEdges)
    (hes : B.1.EdgeOnSide .east e) (hfs : B.1.EdgeOnSide .north f) :
    (segmentTouchGraph D.seamEdges).Reachable ⟨e, he⟩ ⟨f, hf⟩ := by
  let ke : Fin B.1.height.1 := ⟨B.1.height.1 - 1, by have := B.1.height_pos; omega⟩
  let kn : Fin B.1.width.1 := ⟨B.1.width.1 - 1, by have := B.1.width_pos; omega⟩
  have hec : B.1.EdgeOnSide .east (eastSideEdge B.1 heas ke) :=
    (edgeOnEast_iff B.1 heas _).mpr ⟨ke, rfl⟩
  have hnc : B.1.EdgeOnSide .north (northSideEdge B.1 hn kn) :=
    (edgeOnNorth_iff B.1 hn _).mpr ⟨kn, rfl⟩
  exact (same_side_reachable D B .east heas he _ hes hec).trans
    ((eastNorth_adj D B heas hn).reachable.trans
      (same_side_reachable D B .north hn _ hf hnc hfs))

private theorem internal_sides_reachable_of_dims_lt {n : ℕ}
    (D : RectangularPartition n) (B : ↑D.blocks)
    (hwid : B.1.width.1 < n) (hhei : B.1.height.1 < n)
    (s t : RectSide) (hs : B.1.sideInternal s) (ht : B.1.sideInternal t)
    {e f : MacroEdge n} (he : e ∈ D.seamEdges) (hf : f ∈ D.seamEdges)
    (hes : B.1.EdgeOnSide s e) (hft : B.1.EdgeOnSide t f) :
    (segmentTouchGraph D.seamEdges).Reachable ⟨e, he⟩ ⟨f, hf⟩ := by
  cases s <;> cases t
  · exact same_side_reachable D B .west hs he hf hes hft
  · by_cases hys : 0 < B.1.y₀.1
    · let k : Fin B.1.width.1 := ⟨0, B.1.width_pos⟩
      let g := southSideEdge B.1 hys k
      have hg := southSideEdge_mem_seam D B hys k
      have hgs : B.1.EdgeOnSide .south g := (edgeOnSouth_iff B.1 hys g).mpr ⟨k, rfl⟩
      exact (westSouth_reachable D B hs hys he hg hes hgs).trans
        (eastSouth_reachable D B ht hys hf hg hft hgs).symm
    · have hyn : B.1.sideInternal .north := by
        unfold GridRectangle.sideInternal
        have := B.1.y_bound
        omega
      let k : Fin B.1.width.1 := ⟨0, B.1.width_pos⟩
      let g := northSideEdge B.1 hyn k
      have hg := northSideEdge_mem_seam D B hyn k
      have hgn : B.1.EdgeOnSide .north g := (edgeOnNorth_iff B.1 hyn g).mpr ⟨k, rfl⟩
      exact (westNorth_reachable D B hs hyn he hg hes hgn).trans
        (eastNorth_reachable D B ht hyn hf hg hft hgn).symm
  · exact westSouth_reachable D B hs ht he hf hes hft
  · exact westNorth_reachable D B hs ht he hf hes hft
  · by_cases hys : 0 < B.1.y₀.1
    · let k : Fin B.1.width.1 := ⟨0, B.1.width_pos⟩
      let g := southSideEdge B.1 hys k
      have hg := southSideEdge_mem_seam D B hys k
      have hgs : B.1.EdgeOnSide .south g := (edgeOnSouth_iff B.1 hys g).mpr ⟨k, rfl⟩
      exact (eastSouth_reachable D B hs hys he hg hes hgs).trans
        (westSouth_reachable D B ht hys hf hg hft hgs).symm
    · have hyn : B.1.sideInternal .north := by
        unfold GridRectangle.sideInternal
        have := B.1.y_bound
        omega
      let k : Fin B.1.width.1 := ⟨0, B.1.width_pos⟩
      let g := northSideEdge B.1 hyn k
      have hg := northSideEdge_mem_seam D B hyn k
      have hgn : B.1.EdgeOnSide .north g := (edgeOnNorth_iff B.1 hyn g).mpr ⟨k, rfl⟩
      exact (eastNorth_reachable D B hs hyn he hg hes hgn).trans
        (westNorth_reachable D B ht hyn hf hg hft hgn).symm
  · exact same_side_reachable D B .east hs he hf hes hft
  · exact eastSouth_reachable D B hs ht he hf hes hft
  · exact eastNorth_reachable D B hs ht he hf hes hft
  · exact (westSouth_reachable D B ht hs hf he hft hes).symm
  · exact (eastSouth_reachable D B ht hs hf he hft hes).symm
  · exact same_side_reachable D B .south hs he hf hes hft
  · by_cases hxs : 0 < B.1.x₀.1
    · let k : Fin B.1.height.1 := ⟨0, B.1.height_pos⟩
      let g := westSideEdge B.1 hxs k
      have hg := westSideEdge_mem_seam D B hxs k
      have hgw : B.1.EdgeOnSide .west g := (edgeOnWest_iff B.1 hxs g).mpr ⟨k, rfl⟩
      exact (westSouth_reachable D B hxs hs hg he hgw hes).symm.trans
        (westNorth_reachable D B hxs ht hg hf hgw hft)
    · have hxe : B.1.sideInternal .east := by
        unfold GridRectangle.sideInternal
        have := B.1.x_bound
        omega
      let k : Fin B.1.height.1 := ⟨0, B.1.height_pos⟩
      let g := eastSideEdge B.1 hxe k
      have hg := eastSideEdge_mem_seam D B hxe k
      have hge : B.1.EdgeOnSide .east g := (edgeOnEast_iff B.1 hxe g).mpr ⟨k, rfl⟩
      exact (eastSouth_reachable D B hxe hs hg he hge hes).symm.trans
        (eastNorth_reachable D B hxe ht hg hf hge hft)
  · exact (westNorth_reachable D B ht hs hf he hft hes).symm
  · exact (eastNorth_reachable D B ht hs hf he hft hes).symm
  · by_cases hxs : 0 < B.1.x₀.1
    · let k : Fin B.1.height.1 := ⟨0, B.1.height_pos⟩
      let g := westSideEdge B.1 hxs k
      have hg := westSideEdge_mem_seam D B hxs k
      have hgw : B.1.EdgeOnSide .west g := (edgeOnWest_iff B.1 hxs g).mpr ⟨k, rfl⟩
      exact (westNorth_reachable D B hxs hs hg he hgw hes).symm.trans
        (westSouth_reachable D B hxs ht hg hf hgw hft)
    · have hxe : B.1.sideInternal .east := by
        unfold GridRectangle.sideInternal
        have := B.1.x_bound
        omega
      let k : Fin B.1.height.1 := ⟨0, B.1.height_pos⟩
      let g := eastSideEdge B.1 hxe k
      have hg := eastSideEdge_mem_seam D B hxe k
      have hge : B.1.EdgeOnSide .east g := (edgeOnEast_iff B.1 hxe g).mpr ⟨k, rfl⟩
      exact (eastNorth_reachable D B hxe hs hg he hge hes).symm.trans
        (eastSouth_reachable D B hxe ht hg hf hge hft)
  · exact same_side_reachable D B .north hs he hf hes hft

private def Incident {n : ℕ} (B : GridRectangle n) (e : MacroEdge n) : Prop :=
  B.Contains e.lo ∨ B.Contains e.hi

private theorem block_component_dichotomy {n : ℕ}
    (D : RectangularPartition n)
    (c : (segmentTouchGraph D.seamEdges).ConnectedComponent)
    (B : ↑D.blocks)
    (hBc : ∃ e ∈ touchComponentEdges D.seamEdges c, Incident B.1 e) :
    n ≤ (touchComponentEdges D.seamEdges c).card ∨
      ∀ e, e ∈ D.seamEdges → Incident B.1 e →
        e ∈ touchComponentEdges D.seamEdges c := by
  rcases hBc with ⟨e, heC, heInc⟩
  rcases (mem_touchComponentEdges D.seamEdges c e).mp heC with ⟨heD, hec⟩
  obtain ⟨s, hs, hes⟩ := incident_seam_has_internal_side D B heD heInc
  have hside := sideLen_le_component_card D c B s hs heD hec hes
  by_cases hfull : B.1.sideLen s = n
  · left
    simpa [hfull] using hside
  · right
    have hsideLt : B.1.sideLen s < n := by
      have hwle : B.1.width.1 ≤ n := by
        have := B.1.x_bound
        omega
      have hhle : B.1.height.1 ≤ n := by
        have := B.1.y_bound
        omega
      have hle : B.1.sideLen s ≤ n := by
        cases s <;> simp [GridRectangle.sideLen, hwle, hhle]
      omega
    have hwid : B.1.width.1 < n := by
      cases s
      · unfold GridRectangle.sideInternal at hs
        have := B.1.x_bound
        omega
      · unfold GridRectangle.sideInternal at hs
        omega
      · simpa [GridRectangle.sideLen] using hsideLt
      · simpa [GridRectangle.sideLen] using hsideLt
    have hhei : B.1.height.1 < n := by
      cases s
      · simpa [GridRectangle.sideLen] using hsideLt
      · simpa [GridRectangle.sideLen] using hsideLt
      · unfold GridRectangle.sideInternal at hs
        have := B.1.y_bound
        omega
      · unfold GridRectangle.sideInternal at hs
        omega
    intro f hfD hfInc
    obtain ⟨t, ht, hft⟩ := incident_seam_has_internal_side D B hfD hfInc
    have hr := internal_sides_reachable_of_dims_lt D B hwid hhei s t hs ht
      heD hfD hes hft
    apply (mem_touchComponentEdges D.seamEdges c f).mpr
    refine ⟨hfD, ?_⟩
    exact (SimpleGraph.ConnectedComponent.sound hr).symm.trans hec

private theorem block_property_across_edge {n : ℕ}
    (D : RectangularPartition n) (P : ↑D.blocks → Prop)
    (hcross : ∀ e ∈ D.seamEdges,
      (P (D.blockAt e.lo) ↔ P (D.blockAt e.hi)))
    (e : MacroEdge n) : P (D.blockAt e.lo) ↔ P (D.blockAt e.hi) := by
  by_cases he : e ∈ D.seamEdges
  · exact hcross e he
  · have hopen : D.IsOpen e := by
      by_contra hnopen
      exact he (by simpa [RectangularPartition.seamEdges] using hnopen)
    have hEq := D.blockAt_eq_of_sameBlock hopen
    rw [hEq]

private theorem cell_property_iff_origin {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (P : ↑D.blocks → Prop)
    (hedge : ∀ e : MacroEdge n, P (D.blockAt e.lo) ↔ P (D.blockAt e.hi))
    (p : MacroCell n) :
    P (D.blockAt p) ↔ P (D.blockAt (⟨0, hn⟩, ⟨0, hn⟩)) := by
  induction hsum : p.1.1 + p.2.1 using Nat.strong_induction_on generalizing p with
  | h k ih =>
      by_cases hx : p.1.1 = 0
      · by_cases hy : p.2.1 = 0
        · have hp : p = (⟨0, hn⟩, ⟨0, hn⟩) := by
            apply Prod.ext <;> apply Fin.ext <;> assumption
          rw [hp]
        · have hyp : 0 < p.2.1 := Nat.pos_of_ne_zero hy
          let q : MacroCell n := (p.1, ⟨p.2.1 - 1, by omega⟩)
          let e : MacroEdge n := Sum.inr (p.1, ⟨p.2.1 - 1, by omega⟩)
          have helo : e.lo = q := by
            apply Prod.ext <;> apply Fin.ext <;> simp [e, q, MacroEdge.lo]
          have hehi : e.hi = p := by
            apply Prod.ext <;> apply Fin.ext <;> simp [e, MacroEdge.hi] <;> omega
          have hqsum : q.1.1 + q.2.1 < k := by dsimp [q]; omega
          have hiq := ih _ hqsum q rfl
          have heq := hedge e
          rw [helo, hehi] at heq
          exact heq.symm.trans hiq
      · have hxp : 0 < p.1.1 := Nat.pos_of_ne_zero hx
        let q : MacroCell n := (⟨p.1.1 - 1, by omega⟩, p.2)
        let e : MacroEdge n := Sum.inl (⟨p.1.1 - 1, by omega⟩, p.2)
        have helo : e.lo = q := by
          apply Prod.ext <;> apply Fin.ext <;> simp [e, q, MacroEdge.lo]
        have hehi : e.hi = p := by
          apply Prod.ext <;> apply Fin.ext <;> simp [e, MacroEdge.hi] <;> omega
        have hqsum : q.1.1 + q.2.1 < k := by dsimp [q]; omega
        have hiq := ih _ hqsum q rfl
        have heq := hedge e
        rw [helo, hehi] at heq
        exact heq.symm.trans hiq

private theorem block_property_global {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (P : ↑D.blocks → Prop)
    (hcross : ∀ e ∈ D.seamEdges,
      (P (D.blockAt e.lo) ↔ P (D.blockAt e.hi)))
    (hseed : ∃ B : ↑D.blocks, P B) : ∀ B : ↑D.blocks, P B := by
  let origin : MacroCell n := (⟨0, hn⟩, ⟨0, hn⟩)
  have hedge := block_property_across_edge D P hcross
  obtain ⟨B₀, hB₀⟩ := hseed
  let p₀ : MacroCell n := (B₀.1.x₀, B₀.1.y₀)
  have hp₀ : B₀.1.Contains p₀ := by
    unfold GridRectangle.Contains p₀
    simp only [Prod.fst, Prod.snd]
    exact ⟨le_rfl, Nat.lt_add_of_pos_right B₀.1.width_pos,
      le_rfl, Nat.lt_add_of_pos_right B₀.1.height_pos⟩
  have hblock₀ : D.blockAt p₀ = B₀ := D.blockAt_eq_of_contains p₀ B₀ hp₀
  have horigin : P (D.blockAt origin) := by
    have hiff := cell_property_iff_origin hn D P hedge p₀
    exact hiff.mp (hblock₀.symm ▸ hB₀)
  intro B
  let p : MacroCell n := (B.1.x₀, B.1.y₀)
  have hp : B.1.Contains p := by
    unfold GridRectangle.Contains p
    simp only [Prod.fst, Prod.snd]
    exact ⟨le_rfl, Nat.lt_add_of_pos_right B.1.width_pos,
      le_rfl, Nat.lt_add_of_pos_right B.1.height_pos⟩
  have hblock : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
  have hiff := cell_property_iff_origin hn D P hedge p
  exact hblock ▸ hiff.mpr horigin

/-- Fact `e2a3db2ef9d1d6da` (B): every connected component of the
literal seam graph already has at least one full side-length of segments. -/
theorem touchComponent_card_ge {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (hnot : D ≠ wholePartition n hn)
    (c : (segmentTouchGraph D.seamEdges).ConnectedComponent) :
    n ≤ (touchComponentEdges D.seamEdges c).card := by
  by_contra hlarge
  have hsmall : (touchComponentEdges D.seamEdges c).card < n :=
    Nat.lt_of_not_ge hlarge
  let Good : ↑D.blocks → Prop := fun B =>
    ∃ e ∈ touchComponentEdges D.seamEdges c, Incident B.1 e
  have habsorb : ∀ B : ↑D.blocks, Good B → ∀ e, e ∈ D.seamEdges →
      Incident B.1 e → e ∈ touchComponentEdges D.seamEdges c := by
    intro B hB e he hinc
    exact (block_component_dichotomy D c B hB).resolve_left
      (Nat.not_le_of_lt hsmall) e he hinc
  have hseed : ∃ B : ↑D.blocks, Good B := by
    rcases touchComponentEdges_nonempty D.seamEdges c with ⟨e, heC⟩
    rcases (mem_touchComponentEdges D.seamEdges c e).mp heC with ⟨heD, -⟩
    refine ⟨D.blockAt e.lo, e, heC, ?_⟩
    exact Or.inl (D.blockAt_contains e.lo)
  have hcross : ∀ e ∈ D.seamEdges,
      (Good (D.blockAt e.lo) ↔ Good (D.blockAt e.hi)) := by
    intro e he
    constructor
    · intro hgood
      have heC := habsorb (D.blockAt e.lo) hgood e he
        (Or.inl (D.blockAt_contains e.lo))
      exact ⟨e, heC, Or.inr (D.blockAt_contains e.hi)⟩
    · intro hgood
      have heC := habsorb (D.blockAt e.hi) hgood e he
        (Or.inr (D.blockAt_contains e.hi))
      exact ⟨e, heC, Or.inl (D.blockAt_contains e.lo)⟩
  have hall : ∀ B : ↑D.blocks, Good B :=
    block_property_global hn D Good hcross hseed
  have hsub : D.seamEdges ⊆ touchComponentEdges D.seamEdges c := by
    intro e he
    exact habsorb (D.blockAt e.lo) (hall _) e he
      (Or.inl (D.blockAt_contains e.lo))
  have heq : touchComponentEdges D.seamEdges c = D.seamEdges :=
    Finset.Subset.antisymm (touchComponentEdges_subset _ _) hsub
  have hglobal := RectangularPartition.nonwhole_seamCount_ge hn D hnot
  rw [← D.card_seamEdges, ← heq] at hglobal
  exact (Nat.not_le_of_lt hsmall) hglobal

private theorem blockAt_eq_row_forward {n : ℕ} (D : RectangularPartition n)
    (y : Fin n) (x₀ len : ℕ) (hbound : x₀ + len < n)
    (hopen : ∀ k (hk : k < len), D.IsOpen
      (RectangularPartition.horizontalMacroEdge (n := n)
        ⟨x₀ + k, by omega⟩ y)) :
    D.blockAt (⟨x₀, by omega⟩, y) =
      D.blockAt (⟨x₀ + len, hbound⟩, y) := by
  induction len with
  | zero => rfl
  | succ len ih =>
      have hprev : x₀ + len < n := by omega
      have hi := ih hprev (fun k hk => hopen k (by omega))
      have heq := D.blockAt_eq_of_sameBlock (hopen len (by omega))
      have hlo : (RectangularPartition.horizontalMacroEdge (n := n)
          ⟨x₀ + len, by omega⟩ y).lo = (⟨x₀ + len, hprev⟩, y) := by
        apply Prod.ext <;> apply Fin.ext <;> simp [MacroEdge.lo,
          RectangularPartition.horizontalMacroEdge]
      have hhi : (RectangularPartition.horizontalMacroEdge (n := n)
          ⟨x₀ + len, by omega⟩ y).hi = (⟨x₀ + len + 1, by omega⟩, y) := by
        apply Prod.ext <;> apply Fin.ext <;> simp [MacroEdge.hi,
          RectangularPartition.horizontalMacroEdge]
      rw [hlo, hhi] at heq
      exact hi.trans heq

private theorem blockAt_eq_col_forward {n : ℕ} (D : RectangularPartition n)
    (x : Fin n) (y₀ len : ℕ) (hbound : y₀ + len < n)
    (hopen : ∀ k (hk : k < len), D.IsOpen
      (RectangularPartition.verticalMacroEdge (n := n) x
        ⟨y₀ + k, by omega⟩)) :
    D.blockAt (x, ⟨y₀, by omega⟩) =
      D.blockAt (x, ⟨y₀ + len, hbound⟩) := by
  induction len with
  | zero => rfl
  | succ len ih =>
      have hprev : y₀ + len < n := by omega
      have hi := ih hprev (fun k hk => hopen k (by omega))
      have heq := D.blockAt_eq_of_sameBlock (hopen len (by omega))
      have hlo : (RectangularPartition.verticalMacroEdge (n := n) x
          ⟨y₀ + len, by omega⟩).lo = (x, ⟨y₀ + len, hprev⟩) := by
        apply Prod.ext <;> apply Fin.ext <;> simp [MacroEdge.lo,
          RectangularPartition.verticalMacroEdge]
      have hhi : (RectangularPartition.verticalMacroEdge (n := n) x
          ⟨y₀ + len, by omega⟩).hi = (x, ⟨y₀ + len + 1, by omega⟩) := by
        apply Prod.ext <;> apply Fin.ext <;> simp [MacroEdge.hi,
          RectangularPartition.verticalMacroEdge]
      rw [hlo, hhi] at heq
      exact hi.trans heq

private theorem isOpen_transfer_of_seamEdges_eq {n : ℕ}
    (D E : RectangularPartition n) (hseam : D.seamEdges = E.seamEdges)
    (e : MacroEdge n) (hopen : D.IsOpen e) : E.IsOpen e := by
  by_contra hclosed
  have heE : e ∈ E.seamEdges := by simpa [RectangularPartition.seamEdges] using hclosed
  have heD : e ∈ D.seamEdges := by simpa [hseam] using heE
  have hnopen : ¬ D.IsOpen e := by simpa [RectangularPartition.seamEdges] using heD
  exact hnopen hopen

private theorem sameBlock_transfer_of_seamEdges_eq {n : ℕ}
    (D E : RectangularPartition n) (hseam : D.seamEdges = E.seamEdges)
    {p q : MacroCell n} (hpq : D.SameBlock p q) : E.SameBlock p q := by
  rcases hpq with ⟨B, hB, hp, hq⟩
  let r : MacroCell n := (q.1, p.2)
  have hr : B.Contains r := by
    unfold GridRectangle.Contains at hp hq ⊢
    dsimp [r] at ⊢
    omega
  have hrow : E.blockAt p = E.blockAt r := by
    by_cases hxp : p.1.1 ≤ q.1.1
    · let len := q.1.1 - p.1.1
      have hb : p.1.1 + len < n := by dsimp [len]; omega
      have hchain := blockAt_eq_row_forward E p.2 p.1.1 len hb
      have hopen : ∀ k (hk : k < len), E.IsOpen
          (RectangularPartition.horizontalMacroEdge (n := n)
            ⟨p.1.1 + k, by omega⟩ p.2) := by
        intro k hk
        apply isOpen_transfer_of_seamEdges_eq D E hseam
        refine ⟨B, hB, ?_, ?_⟩ <;> unfold GridRectangle.Contains at hp hq ⊢ <;>
          simp only [RectangularPartition.horizontalMacroEdge_lo,
            RectangularPartition.horizontalMacroEdge_hi, Prod.fst, Prod.snd] <;> omega
      have := hchain hopen
      have hend : (⟨p.1.1 + len, hb⟩ : Fin n) = q.1 := by
        apply Fin.ext
        dsimp [len]
        omega
      simpa [r, hend] using this
    · have hqp : q.1.1 ≤ p.1.1 := by omega
      let len := p.1.1 - q.1.1
      have hb : q.1.1 + len < n := by dsimp [len]; omega
      have hchain := blockAt_eq_row_forward E p.2 q.1.1 len hb
      have hopen : ∀ k (hk : k < len), E.IsOpen
          (RectangularPartition.horizontalMacroEdge (n := n)
            ⟨q.1.1 + k, by omega⟩ p.2) := by
        intro k hk
        apply isOpen_transfer_of_seamEdges_eq D E hseam
        refine ⟨B, hB, ?_, ?_⟩ <;> unfold GridRectangle.Contains at hp hq ⊢ <;>
          simp only [RectangularPartition.horizontalMacroEdge_lo,
            RectangularPartition.horizontalMacroEdge_hi, Prod.fst, Prod.snd] <;> omega
      have := hchain hopen
      have hend : (⟨q.1.1 + len, hb⟩ : Fin n) = p.1 := by
        apply Fin.ext
        dsimp [len]
        omega
      simpa [r, hend] using this.symm
  have hcol : E.blockAt r = E.blockAt q := by
    by_cases hyp : p.2.1 ≤ q.2.1
    · let len := q.2.1 - p.2.1
      have hb : p.2.1 + len < n := by dsimp [len]; omega
      have hchain := blockAt_eq_col_forward E q.1 p.2.1 len hb
      have hopen : ∀ k (hk : k < len), E.IsOpen
          (RectangularPartition.verticalMacroEdge (n := n) q.1
            ⟨p.2.1 + k, by omega⟩) := by
        intro k hk
        apply isOpen_transfer_of_seamEdges_eq D E hseam
        refine ⟨B, hB, ?_, ?_⟩ <;> unfold GridRectangle.Contains at hp hq ⊢ <;>
          simp only [RectangularPartition.verticalMacroEdge_lo,
            RectangularPartition.verticalMacroEdge_hi, Prod.fst, Prod.snd] <;> omega
      have := hchain hopen
      have hend : (⟨p.2.1 + len, hb⟩ : Fin n) = q.2 := by
        apply Fin.ext
        dsimp [len]
        omega
      simpa [r, hend] using this
    · have hqp : q.2.1 ≤ p.2.1 := by omega
      let len := p.2.1 - q.2.1
      have hb : q.2.1 + len < n := by dsimp [len]; omega
      have hchain := blockAt_eq_col_forward E q.1 q.2.1 len hb
      have hopen : ∀ k (hk : k < len), E.IsOpen
          (RectangularPartition.verticalMacroEdge (n := n) q.1
            ⟨q.2.1 + k, by omega⟩) := by
        intro k hk
        apply isOpen_transfer_of_seamEdges_eq D E hseam
        refine ⟨B, hB, ?_, ?_⟩ <;> unfold GridRectangle.Contains at hp hq ⊢ <;>
          simp only [RectangularPartition.verticalMacroEdge_lo,
            RectangularPartition.verticalMacroEdge_hi, Prod.fst, Prod.snd] <;> omega
      have := hchain hopen
      have hend : (⟨q.2.1 + len, hb⟩ : Fin n) = p.2 := by
        apply Fin.ext
        dsimp [len]
        omega
      simpa [r, hend] using this.symm
  exact (E.sameBlock_iff_blockAt_eq p q).mpr (hrow.trans hcol)

/-- A rectangular partition is determined by its literal seam set. -/
theorem seamEdges_injective {n : ℕ} :
    Function.Injective (fun D : RectangularPartition n => D.seamEdges) := by
  intro D E h
  apply rectangularPartition_eq_of_sameBlock_iff
  intro p q
  constructor
  · exact sameBlock_transfer_of_seamEdges_eq D E h
  · exact sameBlock_transfer_of_seamEdges_eq E D h.symm

noncomputable def touchComponents {n : ℕ} (M : Finset (MacroEdge n)) :
    Finset (segmentTouchGraph M).ConnectedComponent := Finset.univ

theorem touchComponentEdges_biUnion {n : ℕ} (M : Finset (MacroEdge n)) :
    (touchComponents M).biUnion (touchComponentEdges M) = M := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    rcases Finset.mem_biUnion.mp he with ⟨c, -, hec⟩
    exact touchComponentEdges_subset M c hec
  · intro e he
    let c : (segmentTouchGraph M).ConnectedComponent :=
      (segmentTouchGraph M).connectedComponentMk (⟨e, he⟩ : ↑M)
    apply Finset.mem_biUnion.mpr
    refine ⟨c, (by simp [touchComponents]), ?_⟩
    exact (mem_touchComponentEdges M c e).mpr ⟨he, rfl⟩

theorem touchComponent_card_sum {n : ℕ} (M : Finset (MacroEdge n)) :
    ∑ c ∈ touchComponents M,
      (touchComponentEdges M c).card = M.card := by
  classical
  have hdisj : ∀ c ∈ touchComponents M, ∀ d ∈ touchComponents M,
      c ≠ d → Disjoint (touchComponentEdges M c) (touchComponentEdges M d) := by
    intro c _ d _ hcd
    rw [Finset.disjoint_left]
    intro e hec hed
    rcases (mem_touchComponentEdges M c e).mp hec with ⟨heM, heC⟩
    rcases (mem_touchComponentEdges M d e).mp hed with ⟨_, heD⟩
    apply hcd
    exact heC.symm.trans heD
  calc
    ∑ c ∈ touchComponents M,
        (touchComponentEdges M c).card =
        ((touchComponents M).biUnion (touchComponentEdges M)).card :=
          (Finset.card_biUnion hdisj).symm
    _ = M.card := congrArg Finset.card (touchComponentEdges_biUnion M)

private theorem succ_sq_le_four_pow (n : ℕ) (hn : 0 < n) :
    (n + 1) ^ 2 ≤ 4 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hi := ih (Nat.pos_of_ne_zero hn0)
        calc
          (n + 1 + 1) ^ 2 ≤ 4 * (n + 1) ^ 2 := by nlinarith
          _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 hi
          _ = 4 ^ (n + 1) := by ring

abbrev LargeComposition (n i : ℕ) :=
  {c : Composition i // ∀ j : Fin c.length, n ≤ c.blocksFun j}

abbrev ComponentFamilyCode (n i : ℕ) :=
  Σ c : LargeComposition n i,
    (j : Fin c.1.length) → ConnectedSegmentSet n (c.1.blocksFun j)

noncomputable instance (n i : ℕ) : Fintype (LargeComposition n i) :=
  Fintype.ofFinite _

private theorem card_componentAssignments_le (n i : ℕ) (hn : 0 < n)
    (c : LargeComposition n i) :
    Fintype.card ((j : Fin c.1.length) →
      ConnectedSegmentSet n (c.1.blocksFun j)) ≤ 64 ^ i := by
  classical
  rw [Fintype.card_pi]
  calc
    ∏ j : Fin c.1.length, Fintype.card (ConnectedSegmentSet n (c.1.blocksFun j)) ≤
        ∏ j : Fin c.1.length, 64 ^ (c.1.blocksFun j) := by
      apply Finset.prod_le_prod'
      intro j _
      calc
        Fintype.card (ConnectedSegmentSet n (c.1.blocksFun j)) ≤
            (n + 1) ^ 2 * 16 ^ (c.1.blocksFun j) :=
          card_connectedSegmentSet_le n (c.1.blocksFun j)
        _ ≤ 4 ^ (c.1.blocksFun j) * 16 ^ (c.1.blocksFun j) := by
          exact Nat.mul_le_mul_right _ ((succ_sq_le_four_pow n hn).trans
            (Nat.pow_le_pow_right (by decide) (c.2 j)))
        _ = 64 ^ (c.1.blocksFun j) := by rw [← mul_pow]; norm_num
    _ = 64 ^ i := by
      rw [Finset.prod_pow_eq_pow_sum, Composition.sum_blocksFun]

theorem card_componentFamilyCode_le (n i : ℕ) (hn : 0 < n) :
    Fintype.card (ComponentFamilyCode n i) ≤ 256 ^ i := by
  classical
  change Fintype.card (Σ c : LargeComposition n i,
    (j : Fin c.1.length) → ConnectedSegmentSet n (c.1.blocksFun j)) ≤ 256 ^ i
  rw [Fintype.card_sigma]
  calc
    ∑ c : LargeComposition n i,
        Fintype.card ((j : Fin c.1.length) →
          ConnectedSegmentSet n (c.1.blocksFun j)) ≤
        ∑ _c : LargeComposition n i, 64 ^ i := by
      exact Finset.sum_le_sum fun c _ => card_componentAssignments_le n i hn c
    _ = Fintype.card (LargeComposition n i) * 64 ^ i := by simp
    _ ≤ Fintype.card (Composition i) * 64 ^ i := by
      gcongr
      exact Fintype.card_subtype_le _
    _ = 2 ^ (i - 1) * 64 ^ i := by rw [composition_card]
    _ ≤ 256 ^ i := by
      have hpow : 2 ^ (i - 1) ≤ 4 ^ i := by
        calc
          2 ^ (i - 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.sub_le i 1)
          _ ≤ 4 ^ i := Nat.pow_le_pow_left (by decide) i
      calc
        2 ^ (i - 1) * 64 ^ i ≤ 4 ^ i * 64 ^ i := Nat.mul_le_mul_right _ hpow
        _ = 256 ^ i := by rw [← mul_pow]; norm_num

def decodeComponentFamilyCode {n i : ℕ} (F : ComponentFamilyCode n i) :
    Finset (MacroEdge n) :=
  Finset.univ.biUnion fun j => (F.2 j).1

abbrev NonwholeSeamClass (n : ℕ) (hn : 0 < n) (i : ℕ) :=
  {D : RectangularPartition n // D ≠ wholePartition n hn ∧ D.seamCount = i}

noncomputable instance (n : ℕ) (hn : 0 < n) (i : ℕ) :
    Fintype (NonwholeSeamClass n hn i) := Fintype.ofFinite _

set_option maxHeartbeats 1000000 in
private theorem partitionFamilyCode_exists {n i : ℕ} (hn : 0 < n)
    (D : NonwholeSeamClass n hn i) :
    ∃ F : ComponentFamilyCode n i, decodeComponentFamilyCode F = D.1.seamEdges := by
  classical
  let M : Finset (MacroEdge n) := D.1.seamEdges
  let comps := touchComponents M
  let r := comps.card
  let ord : Fin r ≃ ↑comps := comps.equivFin.symm
  have hsum : ∑ j : Fin r, (touchComponentEdges M (ord j).1).card = i := by
    calc
      ∑ j : Fin r, (touchComponentEdges M (ord j).1).card =
          ∑ x : ↑comps, (touchComponentEdges M x.1).card := by
        exact Fintype.sum_equiv ord _ _ (fun _ => rfl)
      _ = ∑ c ∈ comps, (touchComponentEdges M c).card := by
        change ∑ x ∈ comps.attach, (touchComponentEdges M x.1).card = _
        exact Finset.sum_attach comps (fun c => (touchComponentEdges M c).card)
      _ = M.card := by simpa [comps] using touchComponent_card_sum M
      _ = D.1.seamCount := by
        rw [← D.1.card_seamEdges]
      _ = i := D.2.2
  let prof : Composition i := {
    blocks := List.ofFn (fun j : Fin r => (touchComponentEdges M (ord j).1).card)
    blocks_pos := by
      intro k hk
      rw [List.mem_iff_get] at hk
      rcases hk with ⟨j, rfl⟩
      let j' : Fin r := ⟨j.1, by simpa using j.2⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact Finset.card_pos.mpr (touchComponentEdges_nonempty M (ord j').1)
    blocks_sum := by
      rw [List.sum_ofFn]
      exact hsum
    }
  have hproflen : prof.length = r := by
    change (List.ofFn (fun j : Fin r => (touchComponentEdges M (ord j).1).card)).length = r
    simp
  let ordAt : Fin prof.length → ↑comps := fun j => ord (Fin.cast hproflen j)
  have hprofblock (j : Fin prof.length) :
      prof.blocksFun j = (touchComponentEdges M (ordAt j).1).card := by
    simp [prof, Composition.blocksFun, ordAt] <;>
      congr 3 <;> apply Fin.ext <;> rfl
  have hlarge : ∀ j : Fin prof.length, n ≤ prof.blocksFun j := by
    intro j
    rw [hprofblock j]
    exact touchComponent_card_ge hn D.1 D.2.1 (ordAt j).1
  let large : LargeComposition n i := ⟨prof, hlarge⟩
  let assign : (j : Fin large.1.length) →
      ConnectedSegmentSet n (large.1.blocksFun j) := fun j =>
    ⟨touchComponentEdges M (ordAt j).1,
      by simpa [large] using (hprofblock j).symm,
      touchComponentEdges_segmentConnected M (ordAt j).1⟩
  refine ⟨⟨large, assign⟩, ?_⟩
  unfold decodeComponentFamilyCode
  apply Finset.Subset.antisymm
  · intro e he
    rcases Finset.mem_biUnion.mp he with ⟨j, -, hej⟩
    exact touchComponentEdges_subset M (ordAt j).1 (by simpa [assign] using hej)
  · intro e heM
    let c : (segmentTouchGraph M).ConnectedComponent :=
      (segmentTouchGraph M).connectedComponentMk (⟨e, heM⟩ : ↑M)
    have hc : c ∈ comps := by simp [comps, touchComponents]
    let j₀ : Fin r := comps.equivFin ⟨c, hc⟩
    let j : Fin large.1.length := ⟨j₀.1, by simpa [large, hproflen] using j₀.2⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    have hord : (ordAt j).1 = c := by
      change (ord (Fin.cast hproflen j)).1 = c
      have hjcast : Fin.cast hproflen j = j₀ := by apply Fin.ext; rfl
      rw [hjcast]
      exact congrArg Subtype.val (comps.equivFin.symm_apply_apply ⟨c, hc⟩)
    have hec : e ∈ touchComponentEdges M c :=
      (mem_touchComponentEdges M c e).mpr ⟨heM, rfl⟩
    simpa [assign, hord] using hec

noncomputable def encodeNonwholePartition {n i : ℕ} (hn : 0 < n)
    (D : NonwholeSeamClass n hn i) : ComponentFamilyCode n i :=
  Classical.choose (partitionFamilyCode_exists hn D)

theorem encodeNonwholePartition_spec {n i : ℕ} (hn : 0 < n)
    (D : NonwholeSeamClass n hn i) :
    decodeComponentFamilyCode (encodeNonwholePartition hn D) = D.1.seamEdges :=
  Classical.choose_spec (partitionFamilyCode_exists hn D)

theorem encodeNonwholePartition_injective {n i : ℕ} (hn : 0 < n) :
    Function.Injective (@encodeNonwholePartition n i hn) := by
  intro D E h
  apply Subtype.ext
  apply seamEdges_injective
  calc
    D.1.seamEdges = decodeComponentFamilyCode (encodeNonwholePartition hn D) :=
      (encodeNonwholePartition_spec hn D).symm
    _ = decodeComponentFamilyCode (encodeNonwholePartition hn E) := by rw [h]
    _ = E.1.seamEdges := encodeNonwholePartition_spec hn E

theorem card_nonwholeSeamClass_le (n i : ℕ) (hn : 0 < n) :
    Fintype.card (NonwholeSeamClass n hn i) ≤ 256 ^ i := by
  exact (Fintype.card_le_of_injective (encodeNonwholePartition hn)
    (encodeNonwholePartition_injective hn)).trans (card_componentFamilyCode_le n i hn)

/-- Fact `e2a3db2ef9d1d6da` (C), in exactly the finite-set form consumed by
`RectangularDissectionFacts.census`. -/
theorem rectangularPartition_census (n i : ℕ) (hn : 0 < n) :
    ((Finset.univ.erase (wholePartition n hn)).filter
      (fun D : RectangularPartition n => D.seamCount = i)).card ≤ 256 ^ i := by
  have h := card_nonwholeSeamClass_le n i hn
  calc
    ((Finset.univ.erase (wholePartition n hn)).filter
        (fun D : RectangularPartition n => D.seamCount = i)).card =
        Fintype.card (NonwholeSeamClass n hn i) := by
      rw [Fintype.card_subtype]
      congr 1
      ext D
      simp [and_comm]
    _ ≤ 256 ^ i := h

/-- The two census fields, with no theorem parameter, ready to combine with
the independently formalized perimeter double count. -/
def rectangularDissectionFactsOfPerimeter (n : ℕ) (hn : 0 < n)
    (hperimeter : ∀ D : RectangularPartition n,
      ∑ B : ↑D.blocks, (B.1.width.1 + B.1.height.1) =
        2 * n + D.seamCount) :
    RectangularDissectionFacts n (wholePartition n hn) where
  nonwhole_seam_ge := RectangularPartition.nonwhole_seamCount_ge hn
  census := fun i => rectangularPartition_census n i hn
  perimeter := hperimeter


end

end PakFixedPolyomino
