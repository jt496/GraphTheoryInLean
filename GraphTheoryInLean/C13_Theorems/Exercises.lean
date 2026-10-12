import GraphTheoryInLean.C13_Theorems.C13_Theorems
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
open Finset

/-!
# Exercises
1. Show that a graph with an isolated vertex has no perfect matching.
-/
example (v : V) (hv : ∀ w, ¬ G.Adj v w) :
    ¬ ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

/-!
2. Use Hall's theorem to show that the complete bipartite graph `K[n, n]` has a
perfect matching. Hint: `Sum.swap` maps every set of vertices injectively into its
neighbourhood.
-/
example (n : ℕ) : ∃ M : K[n, n].Subgraph, M.IsPerfectMatching := by
  sorry

/-!
3. Use Hall's theorem to show that the infinite path `pathNat₁` has a perfect
matching. Hint: `n ↦ n + 1` maps every finite set of vertices injectively into its
neighbourhood. What happens for infinite sets?
-/
example : ∃ M : pathNat₁.Subgraph, M.IsPerfectMatching := by
  sorry

/-!
4. Deduce the two-sided version of Hall's theorem: if every vertex lies in `p₁` or
`p₂`, and Hall's condition holds for the subsets of each part, then `G` has a perfect
matching. Why is the hypothesis `hV` needed? Hint: reduce to
`exists_isPerfectMatching_of_forall_ncard_le` by splitting `s` into `s ∩ p₁` and
`s ∩ p₂`, whose neighbourhoods are disjoint.
-/
example [G.LocallyFinite] {p₁ p₂ : Set V} (h₁ : G.IsBipartiteWith p₁ p₂)
    (hV : p₁ ∪ p₂ = Set.univ)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard)
    (h₃ : ∀ s ⊆ p₂, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

/-!
5. Show that the complete graph on a finite type `V` has a perfect matching iff
`Fintype.card V` is even.
-/
example [Fintype V] :
    (∃ M : (⊤ : SimpleGraph V).Subgraph, M.IsPerfectMatching) ↔
      Even (Fintype.card V) := by
  sorry

/-!
6. Show that every vertex has at most two neighbours in the symmetric difference of
two perfect matchings.
-/
example {M M' : G.Subgraph} (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching)
    (v : V) : ((symmDiff M.spanningCoe M'.spanningCoe).neighborSet v).ncard ≤ 2 := by
  sorry

/-!
7. Show that the Turán graph `turanGraph n r` is `r`-colourable for `r > 0`. (So by
Turán's theorem every Turán-maximal `(r + 1)`-clique-free graph is `r`-colourable.)
-/
example (n r : ℕ) (hr : 0 < r) : (turanGraph n r).Colorable r := by
  sorry

/-!
8. Use Mantel's theorem to bound the number of edges of the Mycielskian of a
triangle-free graph.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #mμ[G].edgeFinset ≤ (2 * Fintype.card V + 1) ^ 2 / 4 := by
  sorry

/-!
9. Show that a bipartite graph on `n` vertices has at most `n ^ 2 / 4` edges.
-/
example [Fintype V] [DecidableRel G.Adj] (h : G.IsBipartite) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  sorry

/-!
10. Show that the bound in the Andrásfai–Erdős–Sós theorem cannot be improved for
`r = 2`: the blow-up `C[5][t]` has `n = 5t` vertices and is triangle-free with
minimum degree `2t = 2n / 5`, but it is not bipartite.
-/
example (t : ℕ) :
    C[5][t + 1].CliqueFree 3 ∧ ¬ C[5][t + 1].Colorable 2 ∧
      ∀ v, C[5][t + 1].degree v = 2 * (t + 1) := by
  sorry

/-!
11. Use Zykov's theorem to show that a `4`-clique-free graph on `6` vertices has at
most as many triangles as the octahedron `completeEquipartiteGraph 3 2`. Hint:
Mathlib's `completeEquipartiteGraph.turanGraph` is an isomorphism from
`completeEquipartiteGraph r t` to `turanGraph (r * t) r`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    (h : G.CliqueFree 4) :
    #(G.cliqueFinset 3) ≤ #((completeEquipartiteGraph 3 2).cliqueFinset 3) := by
  sorry

/-!
12. Show that a graph has as many `2`-cliques as edges. Hint: `Sym2.toFinset` sends
the edge `s(x, y)` to `{x, y}`.
-/
lemma card_cliqueFinset_two' [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    #(G.cliqueFinset 2) = #G.edgeFinset := by
  sorry

/-!
13. Deduce the edge bound of Turán's theorem, `CliqueFree.card_edgeFinset_le`, from
Zykov's theorem with `s = 2`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {r : ℕ}
    (h : G.CliqueFree (r + 1)) : #G.edgeFinset ≤ turanNumber (Fintype.card V) r := by
  sorry

/-!
14. Restate Mantel's theorem as a formula for an extremal number.
-/
example (n : ℕ) : extremalNumber n K[3] = n ^ 2 / 4 := by
  sorry

/-!
15. Deduce that a graph on `n` vertices with more than `n ^ 2 / 4` edges contains a
triangle.
-/
example [Fintype V] [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < #G.edgeFinset) : K[3] ⊑ G := by
  sorry

/-!
16. Show that a graph on `n` vertices whose triangles are edge-disjoint has at most
`n.choose 2 / 3` triangles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.EdgeDisjointTriangles) :
    3 * #(G.cliqueFinset 3) ≤ (Fintype.card V).choose 2 := by
  sorry

/-!
17. Let `G` have no triangles and no 5-cycles. Use the count of 5-cycles in `mμ[G]`
from
[Counting 5-Cycles in Mycielskians](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-counting-5-cycles-in-mycielskians)
to bound the number of edges that `killCopies` deletes from `mμ[G]` to make it free
of 5-cycles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (h3 : G.CliqueFree 3)
    (h5 : C[5].Free G) :
    2 * #mμ[G].edgeFinset ≤ 2 * #(mμ[G].killCopies C[5]).edgeFinset +
      ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v := by
  sorry

/-!
18. Show that the grid `hasse ℤ □ hasse ℤ` has exactly one end, as in
[Ends](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-ends). Hint: if
`K` lies in the square `[-N, N] × [-N, N]` then the rows and columns outside the
square avoid `K`. Use `ComponentCompl.mem_of_hom` with `boxProdLeft` and
`boxProdRight` to show that every infinite component of `G - K` contains
`(N + 1, N + 1)`, and apply `subsingleton_end_of_common_vertex`.
-/
example : Nat.card (hasse ℤ □ hasse ℤ).end = 1 := by
  sorry


/-! SOLUTIONS -/

/-!
1. Show that a graph with an isolated vertex has no perfect matching.
-/
example (v : V) (hv : ∀ w, ¬ G.Adj v w) :
    ¬ ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rintro ⟨M, hM⟩
  obtain ⟨w, hw, -⟩ := Subgraph.isPerfectMatching_iff.1 hM v
  exact hv w hw.adj_sub

/-!
2. Use Hall's theorem to show that the complete bipartite graph `K[n, n]` has a
perfect matching. Hint: `Sum.swap` maps every set of vertices injectively into its
neighbourhood.
-/
example (n : ℕ) : ∃ M : K[n, n].Subgraph, M.IsPerfectMatching := by
  refine exists_isPerfectMatching_of_forall_ncard_le
    (IsBipartiteWith.completeBipartiteGraph _ _) fun s => ?_
  refine Set.ncard_le_ncard_of_injOn Sum.swap (fun x hx => ?_)
    Sum.swap_leftInverse.injective.injOn (Set.toFinite _)
  exact Set.mem_biUnion hx (by cases x <;> simp)

/-!
3. Use Hall's theorem to show that the infinite path `pathNat₁` has a perfect
matching. Hint: `n ↦ n + 1` maps every finite set of vertices injectively into its
neighbourhood. What happens for infinite sets?
-/
example : ∃ M : pathNat₁.Subgraph, M.IsPerfectMatching := by
  refine exists_isPerfectMatching_of_forall_ncard_le
    (p₁ := {n | Even n}) (p₂ := {n | Odd n}) ?_ fun s => ?_
  · refine ⟨Set.disjoint_left.2 fun n h1 h2 => Nat.not_even_iff_odd.2 h2 h1, ?_⟩
    rintro v w (rfl | rfl) <;>
      simp [Nat.even_add_one, ← Nat.not_even_iff_odd, em, em']
  · by_cases hs : s.Finite
    · refine Set.ncard_le_ncard_of_injOn (· + 1) (fun x hx => ?_)
        (add_left_injective 1).injOn
        (hs.biUnion fun x _ => (pathNat₁.neighborSet x).toFinite)
      exact Set.mem_biUnion hx (by simp)
    · rw [Set.Infinite.ncard hs]
      exact Nat.zero_le _

/-!
4. Deduce the two-sided version of Hall's theorem: if every vertex lies in `p₁` or
`p₂`, and Hall's condition holds for the subsets of each part, then `G` has a perfect
matching. Why is the hypothesis `hV` needed? Hint: reduce to
`exists_isPerfectMatching_of_forall_ncard_le` by splitting `s` into `s ∩ p₁` and
`s ∩ p₂`, whose neighbourhoods are disjoint.
-/
example [G.LocallyFinite] {p₁ p₂ : Set V} (h₁ : G.IsBipartiteWith p₁ p₂)
    (hV : p₁ ∪ p₂ = Set.univ)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard)
    (h₃ : ∀ s ⊆ p₂, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  -- `hV` is needed: a vertex in neither part has no neighbours, so no perfect
  -- matching covers it, although the one-sided conditions can still hold.
  refine exists_isPerfectMatching_of_forall_ncard_le h₁ fun s => ?_
  rcases s.finite_or_infinite with hs | hs
  · -- split `s` into its parts in `p₁` and `p₂`, whose neighbourhoods are disjoint
    let N : Set V → Set V := fun t => ⋃ x ∈ t, G.neighborSet x
    have hfin {t : Set V} (ht : t ⊆ s) : (N t).Finite :=
      (hs.subset ht).biUnion fun x _ => (G.neighborSet x).toFinite
    have hsplit : s = (s ∩ p₁) ∪ (s ∩ p₂) := by
      rw [← Set.inter_union_distrib_left, hV, Set.inter_univ]
    have hN₁ : N (s ∩ p₁) ⊆ p₂ :=
      Set.iUnion₂_subset fun x hx => isBipartiteWith_neighborSet_subset h₁ hx.2
    have hN₂ : N (s ∩ p₂) ⊆ p₁ :=
      Set.iUnion₂_subset fun x hx => isBipartiteWith_neighborSet_subset h₁.symm hx.2
    calc s.ncard = (s ∩ p₁).ncard + (s ∩ p₂).ncard := by
          conv_lhs => rw [hsplit]
          exact Set.ncard_union_eq
            (h₁.disjoint.mono Set.inter_subset_right Set.inter_subset_right)
            (hs.subset Set.inter_subset_left) (hs.subset Set.inter_subset_left)
      _ ≤ (N (s ∩ p₁)).ncard + (N (s ∩ p₂)).ncard :=
          add_le_add (h₂ _ Set.inter_subset_right) (h₃ _ Set.inter_subset_right)
      _ = (N s).ncard := by
          rw [← Set.ncard_union_eq (h₁.disjoint.symm.mono hN₁ hN₂)
            (hfin Set.inter_subset_left) (hfin Set.inter_subset_left)]
          conv_rhs => rw [hsplit]
          simp only [N, Set.biUnion_union]
  · simp [hs.ncard]

/-!
5. Show that the complete graph on a finite type `V` has a perfect matching iff
`Fintype.card V` is even.
-/
example [Fintype V] :
    (∃ M : (⊤ : SimpleGraph V).Subgraph, M.IsPerfectMatching) ↔
      Even (Fintype.card V) := by
  refine ⟨fun ⟨M, hM⟩ => hM.even_card, fun h => ?_⟩
  have hK : (⊤ : SimpleGraph V).IsClique Set.univ := isClique_univ.2 rfl
  obtain ⟨M, hverts, hM⟩ := (hK.even_iff_exists_isMatching Set.finite_univ).1
    (by rwa [Set.ncard_univ, Nat.card_eq_fintype_card])
  exact ⟨M, hM, Subgraph.isSpanning_iff.2 hverts⟩

/-!
6. Show that every vertex has at most two neighbours in the symmetric difference of
two perfect matchings.
-/
example {M M' : G.Subgraph} (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching)
    (v : V) : ((symmDiff M.spanningCoe M'.spanningCoe).neighborSet v).ncard ≤ 2 := by
  rcases ((symmDiff M.spanningCoe M'.spanningCoe).neighborSet v).eq_empty_or_nonempty
    with h | h
  · simp [h]
  · exact (hM.symmDiff_isCycles hM' h).le

/-!
7. Show that the Turán graph `turanGraph n r` is `r`-colourable for `r > 0`. (So by
Turán's theorem every Turán-maximal `(r + 1)`-clique-free graph is `r`-colourable.)
-/
example (n r : ℕ) (hr : 0 < r) : (turanGraph n r).Colorable r :=
  ⟨Coloring.mk (fun v => ⟨v % r, Nat.mod_lt _ hr⟩) fun h => by
    simpa [Fin.ext_iff] using turanGraph_adj.1 h⟩

/-!
8. Use Mantel's theorem to bound the number of edges of the Mycielskian of a
triangle-free graph.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #mμ[G].edgeFinset ≤ (2 * Fintype.card V + 1) ^ 2 / 4 := by
  have := (CliqueFree.mycielskian h).card_edgeFinset_le (r := 2)
  rwa [turanNumber_two, Fintype.card_option, Fintype.card_sum, ← two_mul]
    at this

/-!
9. Show that a bipartite graph on `n` vertices has at most `n ^ 2 / 4` edges.
-/
example [Fintype V] [DecidableRel G.Adj] (h : G.IsBipartite) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  rw [← turanNumber_two]
  exact (Colorable.cliqueFree h (by norm_num)).card_edgeFinset_le

/-!
10. Show that the bound in the Andrásfai–Erdős–Sós theorem cannot be improved for
`r = 2`: the blow-up `C[5][t]` has `n = 5t` vertices and is triangle-free with
minimum degree `2t = 2n / 5`, but it is not bipartite.
-/
example (t : ℕ) :
    C[5][t + 1].CliqueFree 3 ∧ ¬ C[5][t + 1].Colorable 2 ∧
      ∀ v, C[5][t + 1].degree v = 2 * (t + 1) := by
  refine ⟨(blowUpGraph_cliqueFree_iff _ _ fun _ => 0).2 (by decide), fun h => ?_, ?_⟩
  · have h5 := ((blowUpGraph_colorable_iff _ fun _ => 0).1 h).chromaticNumber_le
    rw [chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)] at h5
    exact absurd h5 (by decide)
  · rintro ⟨v, i⟩
    rw [degree_blowUpN, cycleGraph_degree_three_le, mul_comm]

/-!
11. Use Zykov's theorem to show that a `4`-clique-free graph on `6` vertices has at
most as many triangles as the octahedron `completeEquipartiteGraph 3 2`. Hint:
Mathlib's `completeEquipartiteGraph.turanGraph` is an isomorphism from
`completeEquipartiteGraph r t` to `turanGraph (r * t) r`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    (h : G.CliqueFree 4) :
    #(G.cliqueFinset 3) ≤ #((completeEquipartiteGraph 3 2).cliqueFinset 3) := by
  have e := completeEquipartiteGraph.turanGraph (r := 3) (t := 2)
  have := h.card_cliqueFinset_le (r := 3) 3
  rwa [hV, ← e.card_cliqueFinset_eq] at this

/-!
12. Show that a graph has as many `2`-cliques as edges. Hint: `Sym2.toFinset` sends
the edge `s(x, y)` to `{x, y}`.
-/
/-- A graph has as many `2`-cliques as edges. -/
lemma card_cliqueFinset_two [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    #(G.cliqueFinset 2) = #G.edgeFinset := by
  symm
  refine card_bij (fun e _ => e.toFinset) (fun e he => ?_) (fun e _ e' _ h => ?_)
    (fun t ht => ?_)
  · induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rw [Sym2.toFinset_mk_eq, mem_cliqueFinset_iff]
      exact ⟨by rw [coe_pair]; exact isClique_pair.2 fun _ => he, card_pair he.ne⟩
  · exact Sym2.ext fun x => by rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]
  · rw [mem_cliqueFinset_iff] at ht
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 ht.card_eq
    refine ⟨s(x, y), ?_, Sym2.toFinset_mk_eq⟩
    rw [mem_edgeFinset, mem_edgeSet]
    exact ht.isClique (by simp) (by simp) hxy

/-!
13. Deduce the edge bound of Turán's theorem, `CliqueFree.card_edgeFinset_le`, from
Zykov's theorem with `s = 2`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {r : ℕ}
    (h : G.CliqueFree (r + 1)) : #G.edgeFinset ≤ turanNumber (Fintype.card V) r := by
  have := h.card_cliqueFinset_le 2
  rwa [card_cliqueFinset_two, card_cliqueFinset_two] at this

/-!
14. Restate Mantel's theorem as a formula for an extremal number.
-/
example (n : ℕ) : extremalNumber n K[3] = n ^ 2 / 4 := by
  rw [extremalNumber_top, Fintype.card_fin]
  exact turanNumber_two

/-!
15. Deduce that a graph on `n` vertices with more than `n ^ 2 / 4` edges contains a
triangle.
-/
example [Fintype V] [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < #G.edgeFinset) : K[3] ⊑ G := by
  have h3 : extremalNumber (Fintype.card V) K[3] = Fintype.card V ^ 2 / 4 := by
    rw [extremalNumber_top, Fintype.card_fin]
    exact turanNumber_two
  exact IsContained.of_extremalNumber_lt_card_edgeFinset (h3 ▸ h)

/-!
16. Show that a graph on `n` vertices whose triangles are edge-disjoint has at most
`n.choose 2 / 3` triangles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.EdgeDisjointTriangles) :
    3 * #(G.cliqueFinset 3) ≤ (Fintype.card V).choose 2 :=
  h.card_edgeFinset_le.trans card_edgeFinset_le_card_choose_two

/-!
17. Let `G` have no triangles and no 5-cycles. Use the count of 5-cycles in `mμ[G]`
from
[Counting 5-Cycles in Mycielskians](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-counting-5-cycles-in-mycielskians)
to bound the number of edges that `killCopies` deletes from `mμ[G]` to make it free
of 5-cycles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (h3 : G.CliqueFree 3)
    (h5 : C[5].Free G) :
    2 * #mμ[G].edgeFinset ≤ 2 * #(mμ[G].killCopies C[5]).edgeFinset +
      ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v := by
  rw [← copyCount_mycielskian_cycleGraph_five h3 h5]
  have := le_card_edgeFinset_killCopies_add_copyCount (G := mμ[G]) (H := C[5])
  grind

/-!
18. Show that the grid `hasse ℤ □ hasse ℤ` has exactly one end, as in
[Ends](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-ends). Hint: if
`K` lies in the square `[-N, N] × [-N, N]` then the rows and columns outside the
square avoid `K`. Use `ComponentCompl.mem_of_hom` with `boxProdLeft` and
`boxProdRight` to show that every infinite component of `G - K` contains
`(N + 1, N + 1)`, and apply `subsingleton_end_of_common_vertex`.
-/
example : Nat.card (hasse ℤ □ hasse ℤ).end = 1 := by
  have hadj (n : ℤ) : (hasse ℤ).Adj n (n + 1) :=
    hasse_adj.2 (.inl (Order.covBy_add_one n))
  have hP : (hasse ℤ).Preconnected := hasse_preconnected_of_succ ℤ
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨subsingleton_end_of_common_vertex fun K => ?_, ?_⟩
  · obtain ⟨N, hN⟩ :=
      (K.finite_toSet.image fun v : ℤ × ℤ => max |v.1| |v.2|).bddAbove
    -- the column `{a} × ℤ` and the row `ℤ × {b}` avoid `K` when `N < |a|`, `N < |b|`
    let col (a : ℤ) := (boxProdRight (hasse ℤ) (hasse ℤ) a).toHom
    let row (b : ℤ) := (boxProdLeft (hasse ℤ) (hasse ℤ) b).toHom
    have hcol (a : ℤ) (ha : N < |a|) (n : ℤ) : col a n ∉ K := fun hK =>
      ha.not_ge ((le_max_left _ _).trans (hN ⟨_, hK, rfl⟩))
    have hrow (b : ℤ) (hb : N < |b|) (n : ℤ) : row b n ∉ K := fun hK =>
      hb.not_ge ((le_max_right _ _).trans (hN ⟨_, hK, rfl⟩))
    have hN1 : N < |N + 1| := (lt_add_one N).trans_le (le_abs_self _)
    -- every infinite component of `G - K` contains `(N + 1, N + 1)`
    refine ⟨(N + 1, N + 1), fun C hC => ?_⟩
    obtain ⟨⟨a, b⟩, habC, hbox⟩ :=
      (hC.sdiff ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N))).nonempty
    simp only [Set.mem_prod, Set.mem_Icc, ← abs_le, not_and_or, not_le] at hbox
    rcases hbox with ha | hb
    · have := ComponentCompl.mem_of_hom hP (col a) (hcol a ha) (u := b) habC
      exact ComponentCompl.mem_of_hom hP (row _) (hrow _ hN1) (u := a) (this _) _
    · have := ComponentCompl.mem_of_hom hP (row b) (hrow b hb) (u := a) habC
      exact ComponentCompl.mem_of_hom hP (col _) (hcol _ hN1) (u := b) (this _) _
  · have (n : ℤ) : Fintype ((hasse ℤ).neighborSet n) :=
      Fintype.ofFinset {n - 1, n + 1} fun m => by
        simp [hasse_adj, Order.covBy_iff_add_one_eq]; grind
    have : Fact (hasse ℤ □ hasse ℤ).Preconnected := ⟨hP.boxProd hP⟩
    exact (nonempty_ends_of_infinite _).to_subtype

/-! END SOLUTIONS -/

end SimpleGraph
