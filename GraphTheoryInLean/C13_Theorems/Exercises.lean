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
7. Show that a `k`-regular bipartite graph with `k > 0` has a perfect matching. The
graph need not be finite. Hint: check Hall's condition for a finite set `s` by
counting the edges between `s` and its neighbourhood in two ways, using
`Finset.card_mul_le_card_mul`.
-/
theorem IsRegularOfDegree.exists_isPerfectMatching' [G.LocallyFinite] {k : ℕ}
    (hb : G.IsBipartite) (hG : G.IsRegularOfDegree k) (hk : 0 < k) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

/-!
8. *Kőnig's line colouring theorem* says that a finite bipartite graph `G` has
chromatic index `χ'(G) = Δ(G)` (see
[Edge Colourings](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-edge-colourings)).
Prove it for regular graphs: the edges of a `k`-regular bipartite graph can be
properly coloured with `k` colours. (The general case reduces to this one, since
every finite bipartite graph is a subgraph of a `Δ(G)`-regular bipartite graph.)
Hint: removing a perfect matching leaves a `(k - 1)`-regular bipartite graph, so
induct on `k`. Deduce that the hypercube `Q[n]` has chromatic index `n`.
-/
theorem IsRegularOfDegree.colorable_lineGraph' [G.LocallyFinite] {k : ℕ}
    (hb : G.IsBipartite) (hG : G.IsRegularOfDegree k) : L[G].Colorable k := by
  sorry

example (n : ℕ) : χ L[Q[n]] = n := by
  sorry

/-!
9. Show that the Turán graph `T[n, r]` is `r`-colourable for `r > 0`. (So by Turán's
theorem every Turán-maximal `(r + 1)`-clique-free graph is `r`-colourable.)
-/
example (n r : ℕ) (hr : 0 < r) : T[n, r].Colorable r := by
  sorry

/-!
10. Use Mantel's theorem to bound the number of edges of the Mycielskian of a
triangle-free graph.
-/
example [Fintype V] [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #mμ[G].edgeFinset ≤ (2 * Fintype.card V + 1) ^ 2 / 4 := by
  sorry

/-!
11. Deduce from Füredi's theorem that an `(r + 1)`-clique-free graph with
`turanNumber n r` edges is `r`-colourable. Hint: the subgraph `H` then has as many
edges as `G`, so `H = G` (`eq_of_subset_of_card_le`, `edgeFinset_inj`).
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1))
    (he : #G.edgeFinset = turanNumber (Fintype.card V) r) : G.Colorable r := by
  sorry

/-!
12. Show that the bound in the Andrásfai–Erdős–Sós theorem cannot be improved for
`r = 2`: the blow-up `C[5][t]` has `n = 5t` vertices and is triangle-free with
minimum degree `2t = 2n / 5`, but it is not bipartite.
-/
example (t : ℕ) :
    C[5][t + 1].CliqueFree 3 ∧ ¬ C[5][t + 1].Colorable 2 ∧
      ∀ v, C[5][t + 1].degree v = 2 * (t + 1) := by
  sorry

/-!
13. Restate Mantel's theorem as a formula for an extremal number.
-/
example (n : ℕ) : extremalNumber n K[3] = n ^ 2 / 4 := by
  sorry

/-!
14. Deduce that a graph on `n` vertices with more than `n ^ 2 / 4` edges contains a
triangle.
-/
example [Fintype V] [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < #G.edgeFinset) : K[3] ⊑ G := by
  sorry

/-!
15. Use Zykov's theorem to show that a `4`-clique-free graph on `6` vertices has at
most as many triangles as the octahedron `completeEquipartiteGraph 3 2`. Hint:
Mathlib's `completeEquipartiteGraph.turanGraph` is an isomorphism from
`completeEquipartiteGraph r t` to `turanGraph (r * t) r`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    (h : G.CliqueFree 4) :
    #(G.cliqueFinset 3) ≤ #((completeEquipartiteGraph 3 2).cliqueFinset 3) := by
  sorry

/-!
16. Show that a graph has as many `2`-cliques as edges. Hint: `Sym2.toFinset` sends
the edge `s(x, y)` to `{x, y}`.
-/
lemma card_cliqueFinset_two' [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    #(G.cliqueFinset 2) = #G.edgeFinset := by
  sorry

/-!
17. Deduce the edge bound of Turán's theorem, `CliqueFree.card_edgeFinset_le`, from
Zykov's theorem with `s = 2`.
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ}
    (h : G.CliqueFree (r + 1)) : #G.edgeFinset ≤ turanNumber (Fintype.card V) r := by
  sorry

/-!
18. Show that a graph on `n` vertices whose triangles are edge-disjoint has at most
`n.choose 2 / 3` triangles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.EdgeDisjointTriangles) :
    3 * #(G.cliqueFinset 3) ≤ (Fintype.card V).choose 2 := by
  sorry

/-!
19. The necessity of the Erdős–Gallai conditions (`erdos_gallai`) is a
double-counting argument like those in this chapter. Show that the degrees of any set
`S` of `k` vertices satisfy
`∑ v ∈ S, G.degree v ≤ k * (k - 1) + ∑ v ∈ Sᶜ, min k (G.degree v)`. Hint: split each
degree into the neighbours in `S` and in `Sᶜ` with `degIn_union`, bound the first
part by `k - 1`, and count the edges between `S` and `Sᶜ` from the other side with
`sum_degIn_comm`, as in the proof of Füredi's theorem (`furedi_step`).
-/
theorem sum_degree_le_erdosGallai' [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) :
    ∑ v ∈ S, G.degree v ≤ #S * (#S - 1) + ∑ v ∈ Sᶜ, min #S (G.degree v) := by
  sorry

/-!
20. Deduce that every graphic multiset satisfies the Erdős–Gallai inequalities.
(Together with `Graphic.even_sum` this proves that the conditions in `erdos_gallai`
are necessary.) Hint: first show that a sub-multiset of `s.map f` is the image of a
sub-multiset of `s`, using `Multiset.coe_le` and `List.sublist_map_iff`. Then, with
`L` the sorted list of degrees, realize `L.take k` as the degrees of a set `S` of `k`
vertices, so that `L.drop k` is the list of degrees of `Sᶜ`.
-/
lemma _root_.Multiset.exists_le_map_eq' {α β : Type*} {f : α → β}
    {s : Multiset α} {t : Multiset β} (h : t ≤ s.map f) : ∃ u ≤ s, u.map f = t := by
  sorry

theorem Graphic.erdosGallaiLE' {m : Multiset ℕ} (h : Graphic m) {k : ℕ}
    (hk : k ≤ m.card) : ErdosGallaiLE m k := by
  sorry

/-!
21. Show that the grid `hasse ℤ □ hasse ℤ` has exactly one end, as in
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
          nth_rw 1 [hsplit]
          exact Set.ncard_union_eq
            (h₁.disjoint.mono Set.inter_subset_right Set.inter_subset_right)
            (hs.subset Set.inter_subset_left) (hs.subset Set.inter_subset_left)
      _ ≤ (N (s ∩ p₁)).ncard + (N (s ∩ p₂)).ncard :=
          add_le_add (h₂ _ Set.inter_subset_right) (h₃ _ Set.inter_subset_right)
      _ = (N s).ncard := by
          rw [← Set.ncard_union_eq (h₁.disjoint.symm.mono hN₁ hN₂)
            (hfin Set.inter_subset_left) (hfin Set.inter_subset_left)]
          nth_rw 3 [hsplit]
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
7. Show that a `k`-regular bipartite graph with `k > 0` has a perfect matching. The
graph need not be finite. Hint: check Hall's condition for a finite set `s` by
counting the edges between `s` and its neighbourhood in two ways, using
`Finset.card_mul_le_card_mul`.
-/
/-- A `k`-regular bipartite graph with `k > 0` has a perfect matching. -/
theorem IsRegularOfDegree.exists_isPerfectMatching [G.LocallyFinite] {k : ℕ}
    (hb : G.IsBipartite) (hG : G.IsRegularOfDegree k) (hk : 0 < k) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨p₁, p₂, h₁⟩ := hb.exists_isBipartiteWith
  refine exists_isPerfectMatching_of_forall_ncard_le h₁ fun s => ?_
  classical
  rcases s.finite_or_infinite with hs | hs
  · -- `s` sends `k * |s|` edges to `N`, and each vertex of `N` receives at most `k`
    let t := hs.toFinset
    let N := t.biUnion fun x => G.neighborFinset x
    have hN : ⋃ x ∈ s, G.neighborSet x = N := by ext; simp [N, t]
    have hcount : #t * k ≤ #N * k := by
      refine card_mul_le_card_mul G.Adj (fun a ha => ?_) (fun b _ => ?_)
      · -- each `a ∈ t` has all `k` of its neighbours in `N`
        have hsub : G.neighborFinset a ⊆ N :=
          subset_biUnion_of_mem (fun x => G.neighborFinset x) ha
        exact (hG a).ge.trans (degIn_eq_degree hsub).ge
      · -- each `b ∈ N` has at most `k` neighbours in `t`
        rw [← G.degIn_eq_card_bipartiteBelow, ← hG b]
        exact degIn_le_degree t b
    rw [hN, Set.ncard_coe_finset, Set.ncard_eq_toFinset_card s hs]
    exact Nat.le_of_mul_le_mul_right hcount hk
  · simp [hs.ncard]

/-!
8. *Kőnig's line colouring theorem* says that a finite bipartite graph `G` has
chromatic index `χ'(G) = Δ(G)` (see
[Edge Colourings](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-edge-colourings)).
Prove it for regular graphs: the edges of a `k`-regular bipartite graph can be
properly coloured with `k` colours. (The general case reduces to this one, since
every finite bipartite graph is a subgraph of a `Δ(G)`-regular bipartite graph.)
Hint: removing a perfect matching leaves a `(k - 1)`-regular bipartite graph, so
induct on `k`. Deduce that the hypercube `Q[n]` has chromatic index `n`.
-/
/-- *Kőnig's line colouring theorem* for regular graphs: the edges of a
`k`-regular bipartite graph can be properly coloured with `k` colours. -/
theorem IsRegularOfDegree.colorable_lineGraph [G.LocallyFinite] {k : ℕ}
    (hb : G.IsBipartite) (hG : G.IsRegularOfDegree k) : L[G].Colorable k := by
  classical
  induction k generalizing G with
  | zero =>
    -- a `0`-regular graph has no edges
    refine colorable_zero_iff.2 ⟨fun ⟨e, he⟩ => ?_⟩
    induction e using Sym2.ind with | h a b => ?_
    have := hG a
    rw [← ncard_neighborSet, Set.ncard_eq_zero (Set.toFinite _)] at this
    exact this.subset (mem_neighborSet _ _ _ |>.2 he)
  | succ k ih =>
    -- remove a perfect matching `M`
    obtain ⟨M, hM⟩ := hG.exists_isPerfectMatching hb k.succ_pos
    let G' := G \ M.spanningCoe
    have hle : G' ≤ G := sdiff_le
    let : G'.LocallyFinite := fun v =>
      ((G.neighborSet v).toFinite.subset fun w hw => hle hw).fintype
    -- what is left is `k`-regular
    have hG' : G'.IsRegularOfDegree k := fun v => by
      obtain ⟨w, hw, hw'⟩ := Subgraph.isPerfectMatching_iff.1 hM v
      have : G'.neighborSet v = G.neighborSet v \ {w} := by
        ext x
        have hMx : M.Adj v x ↔ x = w := ⟨hw' x, fun h => h ▸ hw⟩
        simp only [G', mem_neighborSet, sdiff_adj, Subgraph.spanningCoe_adj,
          Set.mem_sdiff, Set.mem_singleton_iff, hMx]
      rw [← ncard_neighborSet, this,
        Set.ncard_sdiff_singleton_of_mem ((G.mem_neighborSet v w).2 hw.adj_sub),
        ncard_neighborSet, hG v, Nat.add_sub_cancel]
    obtain ⟨C⟩ := ih (hb.mono_left hle) hG'
    -- colour the edges of `M` with the new colour `k`
    have hmem {e : Sym2 V} (he : e ∈ G.edgeSet) (heM : e ∉ M.edgeSet) :
        e ∈ G'.edgeSet := by
      simpa [G', edgeSet_sdiff, he] using heM
    refine ⟨Coloring.mk (fun e => if h : (e : Sym2 V) ∈ M.edgeSet then Fin.last k
      else (C ⟨e, hmem e.2 h⟩).castSucc) ?_⟩
    rintro ⟨e, he⟩ ⟨f, hf⟩ ⟨hne, x, hxe, hxf⟩
    by_cases heM : e ∈ M.edgeSet <;> by_cases hfM : f ∈ M.edgeSet <;>
      simp only [heM, hfM, dite_true, dite_false, ne_eq]
    · -- two edges of a matching sharing the vertex `x` are equal
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hxe
      obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 hxf
      obtain rfl := hM.1.eq_of_adj_left heM hfM
      exact (hne rfl).elim
    · -- `e` has the new colour `k`, `f` an old colour
      exact (Fin.castSucc_ne_last _).symm
    · -- `f` has the new colour `k`, `e` an old colour
      exact Fin.castSucc_ne_last _
    · -- both edges keep their colours from `C`, and they are adjacent in `L[G']`
      have hadj : L[G'].Adj ⟨e, hmem he heM⟩ ⟨f, hmem hf hfM⟩ :=
        ⟨by simpa using hne, x, hxe, hxf⟩
      exact Fin.castSucc_injective _ |>.ne (C.valid hadj)

example (n : ℕ) : χ L[Q[n]] = n := by
  have hG := IsRegularOfDegree.hypercube n
  refine le_antisymm ((hG.colorable_lineGraph (IsBipartite.hypercube n))
    |>.chromaticNumber_le) ?_
  have := Q[n].degree_le_chromaticNumber_lineGraph (Classical.arbitrary _)
  rwa [hG] at this

/-!
9. Show that the Turán graph `T[n, r]` is `r`-colourable for `r > 0`. (So by Turán's
theorem every Turán-maximal `(r + 1)`-clique-free graph is `r`-colourable.)
-/
example (n r : ℕ) (hr : 0 < r) : T[n, r].Colorable r :=
  ⟨Coloring.mk (fun v => ⟨v % r, Nat.mod_lt _ hr⟩) fun h => by
    simpa [Fin.ext_iff] using turanGraph_adj.1 h⟩

/-!
10. Use Mantel's theorem to bound the number of edges of the Mycielskian of a
triangle-free graph.
-/
example [Fintype V] [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #mμ[G].edgeFinset ≤ (2 * Fintype.card V + 1) ^ 2 / 4 := by
  have := (CliqueFree.mycielskian h).card_edgeFinset_le (r := 2)
  rwa [turanNumber_two, Fintype.card_option, Fintype.card_sum, ← two_mul]
    at this

/-!
11. Deduce from Füredi's theorem that an `(r + 1)`-clique-free graph with
`turanNumber n r` edges is `r`-colourable. Hint: the subgraph `H` then has as many
edges as `G`, so `H = G` (`eq_of_subset_of_card_le`, `edgeFinset_inj`).
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1))
    (he : #G.edgeFinset = turanNumber (Fintype.card V) r) : G.Colorable r := by
  obtain ⟨H, _, hHG, hH, h2⟩ := h.exists_colorable_two_mul_card_edgeFinset_le
  have hsub := edgeFinset_mono hHG
  have : H.edgeFinset = G.edgeFinset := eq_of_subset_of_card_le hsub (by grind)
  rwa [edgeFinset_inj.1 this] at hH

/-!
12. Show that the bound in the Andrásfai–Erdős–Sós theorem cannot be improved for
`r = 2`: the blow-up `C[5][t]` has `n = 5t` vertices and is triangle-free with
minimum degree `2t = 2n / 5`, but it is not bipartite.
-/
example (t : ℕ) :
    C[5][t + 1].CliqueFree 3 ∧ ¬ C[5][t + 1].Colorable 2 ∧
      ∀ v, C[5][t + 1].degree v = 2 * (t + 1) := by
  refine ⟨(cliqueFree_blowUpGraph_iff _ _ fun _ => 0).2 (by decide), fun h => ?_, ?_⟩
  · have h5 := ((colorable_blowUpGraph_iff _ fun _ => 0).1 h).chromaticNumber_le
    rw [chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)] at h5
    exact absurd h5 (by decide)
  · rintro ⟨v, i⟩
    rw [degree_blowUpN, cycleGraph_degree_three_le, mul_comm]

/-!
13. Restate Mantel's theorem as a formula for an extremal number.
-/
example (n : ℕ) : extremalNumber n K[3] = n ^ 2 / 4 := by
  rw [extremalNumber_top, Fintype.card_fin]
  exact turanNumber_two

/-!
14. Deduce that a graph on `n` vertices with more than `n ^ 2 / 4` edges contains a
triangle.
-/
example [Fintype V] [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < #G.edgeFinset) : K[3] ⊑ G := by
  have h3 : extremalNumber (Fintype.card V) K[3] = Fintype.card V ^ 2 / 4 := by
    rw [extremalNumber_top, Fintype.card_fin]
    exact turanNumber_two
  exact IsContained.of_extremalNumber_lt_card_edgeFinset (h3 ▸ h)

/-!
15. Use Zykov's theorem to show that a `4`-clique-free graph on `6` vertices has at
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
16. Show that a graph has as many `2`-cliques as edges. Hint: `Sym2.toFinset` sends
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
17. Deduce the edge bound of Turán's theorem, `CliqueFree.card_edgeFinset_le`, from
Zykov's theorem with `s = 2`.
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ}
    (h : G.CliqueFree (r + 1)) : #G.edgeFinset ≤ turanNumber (Fintype.card V) r := by
  classical
  have := h.card_cliqueFinset_le 2
  rwa [card_cliqueFinset_two, card_cliqueFinset_two] at this

/-!
18. Show that a graph on `n` vertices whose triangles are edge-disjoint has at most
`n.choose 2 / 3` triangles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.EdgeDisjointTriangles) :
    3 * #(G.cliqueFinset 3) ≤ (Fintype.card V).choose 2 :=
  h.card_edgeFinset_le.trans card_edgeFinset_le_card_choose_two

/-!
19. The necessity of the Erdős–Gallai conditions (`erdos_gallai`) is a
double-counting argument like those in this chapter. Show that the degrees of any set
`S` of `k` vertices satisfy
`∑ v ∈ S, G.degree v ≤ k * (k - 1) + ∑ v ∈ Sᶜ, min k (G.degree v)`. Hint: split each
degree into the neighbours in `S` and in `Sᶜ` with `degIn_union`, bound the first
part by `k - 1`, and count the edges between `S` and `Sᶜ` from the other side with
`sum_degIn_comm`, as in the proof of Füredi's theorem (`furedi_step`).
-/
theorem sum_degree_le_erdosGallai [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) :
    ∑ v ∈ S, G.degree v ≤ #S * (#S - 1) + ∑ v ∈ Sᶜ, min #S (G.degree v) := by
  -- each degree splits into the neighbours in `S` and those in `Sᶜ`
  have hsplit (v : V) : G.degree v = G.degIn S v + G.degIn Sᶜ v := by
    rw [← degIn_union _ _ _ disjoint_compl_right, union_compl, degIn_eq_card_filter,
      ← card_neighborFinset_eq_degree]
    congr 1; ext; simp
  -- a vertex of `S` has at most `#S - 1` neighbours in `S`
  have h1 : ∑ v ∈ S, G.degIn S v ≤ #S * (#S - 1) := by
    rw [← smul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun v hv => ?_
    calc G.degIn S v ≤ #(S.erase v) := card_le_card fun w hw => by
            rw [mem_bipartiteAbove] at hw
            exact mem_erase.2 ⟨(G.ne_of_adj hw.2).symm, hw.1⟩
      _ = #S - 1 := card_erase_of_mem hv
  -- count the edges between `S` and `Sᶜ` from the `Sᶜ` side
  have h2 : ∑ v ∈ S, G.degIn Sᶜ v ≤ ∑ v ∈ Sᶜ, min #S (G.degree v) := by
    rw [sum_degIn_comm]
    exact sum_le_sum fun v _ => le_min (card_filter_le _ _) (degIn_le_degree _ _)
  rw [sum_congr rfl fun v _ => hsplit v, sum_add_distrib]
  grind

/-!
20. Deduce that every graphic multiset satisfies the Erdős–Gallai inequalities.
(Together with `Graphic.even_sum` this proves that the conditions in `erdos_gallai`
are necessary.) Hint: first show that a sub-multiset of `s.map f` is the image of a
sub-multiset of `s`, using `Multiset.coe_le` and `List.sublist_map_iff`. Then, with
`L` the sorted list of degrees, realize `L.take k` as the degrees of a set `S` of `k`
vertices, so that `L.drop k` is the list of degrees of `Sᶜ`.
-/
lemma _root_.Multiset.exists_le_map_eq {α β : Type*} {f : α → β}
    {s : Multiset α} {t : Multiset β} (h : t ≤ s.map f) : ∃ u ≤ s, u.map f = t := by
  induction s using Quotient.inductionOn
  induction t using Quotient.inductionOn
  obtain ⟨l', hp, hs⟩ := Multiset.coe_le.1 h
  obtain ⟨l'', hl'', rfl⟩ := List.sublist_map_iff.1 hs
  exact ⟨l'', Multiset.coe_le.2 hl''.subperm, Multiset.coe_eq_coe.2 hp⟩

theorem Graphic.erdosGallaiLE {m : Multiset ℕ} (h : Graphic m) {k : ℕ}
    (hk : k ≤ m.card) : ErdosGallaiLE m k := by
  obtain ⟨V, _, G, _, rfl⟩ := h
  classical
  set L := G.degreeMultiset.sort (· ≥ ·)
  have hL : (L.take k : Multiset ℕ) + L.drop k = G.degreeMultiset := by
    rw [Multiset.coe_add, List.take_append_drop, Multiset.sort_eq]
  -- `L.take k` is the multiset of degrees of a set `S` of vertices
  obtain ⟨u, hu, hmap⟩ := Multiset.exists_le_map_eq
    (hL ▸ Multiset.le_add_right _ _ : (L.take k : Multiset ℕ) ≤ G.degreeMultiset)
  let S : Finset V := ⟨u, Multiset.nodup_of_le hu univ.nodup⟩
  have hS : #S = k := by
    rw [card_mk, ← Multiset.card_map, hmap, Multiset.coe_card,
      List.length_take, Multiset.length_sort]
    exact min_eq_left hk
  -- and `L.drop k` is the multiset of degrees of `Sᶜ`
  have hc : Sᶜ.val.map (G.degree ·) = (L.drop k : Multiset ℕ) := by
    have := hL
    rw [degreeMultiset, ← union_compl S,
      ← disjUnion_eq_union _ _ disjoint_compl_right, disjUnion_val,
      Multiset.map_add] at this
    exact (add_left_cancel (this.trans (by rw [← hmap]))).symm
  calc (L.take k).sum = ∑ v ∈ S, G.degree v := by
        rw [← Multiset.sum_coe, ← hmap]; rfl
    _ ≤ k * (k - 1) + ∑ v ∈ Sᶜ, min k (G.degree v) :=
        hS ▸ sum_degree_le_erdosGallai S
    _ = _ := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, ← hc, Multiset.map_map]; rfl

/-!
21. Show that the grid `hasse ℤ □ hasse ℤ` has exactly one end, as in
[Ends](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-ends). Hint: if
`K` lies in the square `[-N, N] × [-N, N]` then the rows and columns outside the
square avoid `K`. Use `ComponentCompl.mem_of_hom` with `boxProdLeft` and
`boxProdRight` to show that every infinite component of `G - K` contains
`(N + 1, N + 1)`, and apply `subsingleton_end_of_common_vertex`.
-/
example : Nat.card (hasse ℤ □ hasse ℤ).end = 1 := by
  have hadj (n : ℤ) : (hasse ℤ).Adj n (n + 1) :=
    hasse_adj.2 (.inl (Order.covBy_add_one n))
  have hP : (hasse ℤ).Preconnected := preconnected_hasse_of_succOrder ℤ
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
