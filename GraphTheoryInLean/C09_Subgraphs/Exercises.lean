import GraphTheoryInLean.C09_Subgraphs.C09_Subgraphs
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
/-!
# Exercises

1. If `H` and `K` are complementary subgraphs of `G` (i.e. `IsCompl H K`, which
packages `H ⊓ K = ⊥` and `H ⊔ K = ⊤`) then no edge of `G` can have only one
endpoint in `H`.
-/
lemma Subgraph.mem_verts_iff_of_isCompl' {H K : G.Subgraph} (h : IsCompl H K)
    {v w : V} (hadj : G.Adj v w) : v ∈ H.verts ↔ w ∈ H.verts := by
  sorry

/-!
2. Prove that the *Heyting complement* of a subgraph `H` (which is how `Hᶜ` is
defined) is `(⊤ : G.Subgraph).induce H.vertsᶜ`
-/
example (H : G.Subgraph) : Hᶜ = (⊤ : G.Subgraph).induce H.vertsᶜ := by
  sorry

/-!
3. Show that any edge of an induced subgraph is an edge of `G`.
-/
example (s : Set V) (v w : V) (h : ((⊤ : G.Subgraph).induce s).Adj v w) :
    G.Adj v w := by
  sorry

/-!
4. Show that the induced subgraph on `Set.univ` is the `top` subgraph.
-/
example : (⊤ : G.Subgraph).induce Set.univ = ⊤ := by
  sorry

/-!
5. Show that the single-edge subgraph `G.subgraphOfAdj hadj` is a subgraph of a
subgraph `H` if and only if `H` contains the edge.
-/
example {v w : V} (hadj : G.Adj v w) (H : G.Subgraph) :
    G.subgraphOfAdj hadj ≤ H ↔ H.Adj v w := by
  sorry

/-!
6. Show that an induced subgraph `(⊤ : G.Subgraph).induce s` is induced (in the sense
of `Subgraph.IsInduced`).
-/
example (s : Set V) : ((⊤ : G.Subgraph).induce s).IsInduced := by
  sorry

/-!
7. Show that the spanning coercion of a single vertex subgraph is the empty graph
`⊥ : SimpleGraph V`, which has every vertex of `V`. So `spanningCoe` forgets the
vertex set of a subgraph.
-/
example (v : V) : (G.singletonSubgraph v).spanningCoe = ⊥ := by
  sorry

/-!
8. Show that if every induced subgraph of `G` on a finite set of vertices is
`n`-colourable then `G` is `n`-colourable. Hint: use the De Bruijn–Erdős theorem
`colorable_of_forall_finite_subgraph_colorable`. For a finite subgraph `H`, the graph
`H.coe` is a subgraph of `G.induce H.verts` on the same vertex type `↑H.verts`, so
`Colorable.mono_left` applies.
-/
lemma colorable_of_forall_finite_induce_colorable' {n : ℕ}
    (h : ∀ s : Set V, s.Finite → (G.induce s).Colorable n) : G.Colorable n := by
  sorry

/-!
9. Show that the matching number is monotone: if `G ≤ H` then `ν G ≤ ν H`. Hint:
turn a matching of `G` into a matching of `H` with the same edges by building the
`H.Subgraph` directly, then use the `matchingNum` API (`matchingNum_le` and
`Subgraph.IsMatching.le_matchingNum`). (Mathlib's `Subgraph.IsMatching.map_ofLE`
says that `M.map (Hom.ofLE h)` is a matching of `H`, but its edges are then harder
to count.)
-/
lemma matchingNum_mono' {G H : SimpleGraph V} (h : G ≤ H) :
    ν G ≤ ν H := by
  sorry

/-!
10. Show that `ν K[3] = 1` but `τ K[3] = 2`, so weak duality `ν G ≤ τ G` can be
strict. Hint: for the first, `matchingNum_le_card_div_two` gives the upper bound and
a single edge is a matching (`Subgraph.IsMatching.subgraphOfAdj`). For the second,
use Mathlib's `vertexCoverNum_top`.
-/
example : ν K[3] = 1 := by
  sorry

example : τ K[3] = 2 := by
  sorry

/-!
11. Show that the infinite path has matching number `⊤`. Hint: build the subgraph of
`pathNat₁` that pairs `2 * k` with `2 * k + 1`. (An easy way to define this adjacency
relation is as `pathNat₁.Adj m n ∧ m / 2 = n / 2`.) Show that it is a matching, and
show that its edge set is infinite (`Set.infinite_of_injective_forall_mem`).
-/
lemma matchingNum_pathNat₁' : ν pathNat₁ = ⊤ := by
  sorry

/-!
12. Show that in a finite graph `⍺ G + ν G ≤ |V|`. Hint: let `I` be a maximum
independent set (`exists_isNIndepSet_indepNum`) and `M` a maximum matching
(`exists_isMatching_matchingNum`), so `#I = ⍺ G` and `M` has `ν G` edges. Count the
vertices of `I` inside and outside `M.verts` separately:
* *Inside:* no edge of `M` has both ends in `I`, since `I` is independent. So
  sending each `v ∈ I ∩ M.verts` to the edge of `M` containing it is injective, and
  at most `|E(M)|` vertices of `I` lie in `M.verts`
  (`Subgraph.IsMatching.ncard_inter_le_of_isIndepSet`).
* *Outside:* `M.verts` has `2 * |E(M)|` vertices (`Subgraph.IsMatching.ncard_verts`),
  so at most `|V| - 2 * |E(M)|` vertices lie outside it.

Adding these gives `⍺ G ≤ |V| - |E(M)|`. To do the arithmetic in `ℕ`, write `ν G` as
the cast of `M.edgeSet.ncard` using `Set.coe_ncard_eq_encard`.
-/
lemma indepNum_add_matchingNum_le' [Finite V] :
    (⍺ G : ℕ∞) + ν G ≤ Nat.card V := by
  sorry

/-!
13. Deduce that `⍺ Q[n + 1] ≤ 2 ^ n`. (In fact `⍺ Q[n + 1] = 2 ^ n`: the vertices
with an even number of `1`s form an independent set.)
-/
example (n : ℕ) : ⍺ Q[n + 1] ≤ 2 ^ n := by
  sorry

/-!
14. The supremum of an increasing sequence of matchings is a matching. Hint: a
vertex of `⨆ n, M n` lies in some `M n` (`Subgraph.verts_iSup`) and an edge of
`⨆ n, M n` lies in some `M m` (`Subgraph.iSup_adj`); compare the two at the later
stage `max n m`.
-/
lemma Subgraph.IsMatching.iSup_of_monotone' {M : ℕ → G.Subgraph}
    (hmono : Monotone M) (hM : ∀ n, (M n).IsMatching) : (⨆ n, M n).IsMatching := by
  sorry

/-!
15. If `ν G = ⊤` then every finite set of vertices `S` misses some edge of `G`.
Hint: otherwise `S` is a vertex cover, so weak duality
(`matchingNum_le_vertexCoverNum`) and `IsVertexCover.vertexCoverNum_le` force
`S.encard = ⊤`.
-/
lemma exists_adj_notMem_of_matchingNum_eq_top' (h : ν G = ⊤) {S : Set V}
    (hS : S.Finite) : ∃ a b, G.Adj a b ∧ a ∉ S ∧ b ∉ S := by
  sorry

/-!
16. A matching `M` with finitely many vertices in a graph with `ν G = ⊤` can be
extended by one edge. Hint: take an edge avoiding `M.verts` from the previous
exercise and add it with `Subgraph.IsMatching.sup`, whose disjointness hypothesis
is about supports (`Subgraph.IsMatching.support_eq_verts`), then count edges with
`Set.encard_insert_of_notMem`.
-/
lemma Subgraph.IsMatching.exists_le_encard_eq_add_one' (h : ν G = ⊤)
    {M : G.Subgraph} (hM : M.IsMatching) (hfin : M.verts.Finite) :
    ∃ N : G.Subgraph, M ≤ N ∧ N.IsMatching ∧ N.verts.Finite ∧
      N.edgeSet.encard = M.edgeSet.encard + 1 := by
  sorry

/-!
17. If `ν G = ⊤` then `G` has an infinite matching. Hint: restate the previous
exercise on the subtype `FM := {M : G.Subgraph // M.IsMatching ∧ M.verts.Finite}`
of finite matchings, so that `choose` produces a step function `next : FM → FM`,
and iterate it from `⊥`: `M n := next^[n] ⊥`, with `Function.iterate_succ_apply'`
unfolding one step. Each `M n` is then a finite matching by construction; show by
induction that it has exactly `n` edges. Each step extends the previous matching, so
`M` is monotone (`monotone_nat_of_le_succ`) and `⨆ n, M n` is a matching by
Exercise 14 with at least `n` edges for every `n`.
-/
lemma exists_isMatching_encard_eq_top' (h : ν G = ⊤) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = ⊤ := by
  -- Choose, for every finite matching, an extension by one edge. Packaging the
  -- finite matchings as a subtype `FM` makes this a total function `next`.
  let FM := {M : G.Subgraph // M.IsMatching ∧ M.verts.Finite}
  have : ∀ M : FM, ∃ N : FM,
      M.1 ≤ N.1 ∧ N.1.edgeSet.encard = M.1.edgeSet.encard + 1 := by
    rintro ⟨M, hM, hfin⟩
    obtain ⟨N, hle, hN, hNfin, hcard⟩ := hM.exists_le_encard_eq_add_one' h hfin
    exact ⟨⟨N, hN, hNfin⟩, hle, hcard⟩
  choose next hnext hcard using this
  -- Iterate from the empty matching.
  let M : ℕ → FM := fun n => next^[n] ⟨⊥, Subgraph.isMatching_bot, by simp⟩
  have hstep : ∀ n, M (n + 1) = next (M n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  -- Each `M n` is a finite matching by construction; it has exactly `n` edges.
  sorry

/-!
18. Conclude that the matching number is attained in every graph, finite or not:
this is the analogue of Mathlib's `vertexCoverNum_exists`. Hint: if `ν G = ⊤` use
the previous exercise; otherwise a finite supremum in `ℕ∞` is attained
(`ENat.exists_eq_iSup_of_lt_top`), exactly as in the proof of
`exists_isMatching_matchingNum`.
-/
lemma matchingNum_exists' (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = ν G := by
  sorry

/-!
19. Show that, provided there is at least one colour, `s` is `n`-colourable in the
sense of `ColorableOn` iff the induced subgraph `G.induce s` is `n`-colourable. (So
partial colourings really do capture colourings of induced subgraphs.) Why is the
hypothesis `0 < n` needed?
-/
lemma colorableOn_iff_colorable_induce' {n : ℕ} (hn : 0 < n) (s : Set V) :
    G.ColorableOn n s ↔ (G.induce s).Colorable n := by
  sorry

/-! SOLUTIONS -/

/-!
1. If `H` and `K` are complementary subgraphs of `G` (i.e. `IsCompl H K`, which
packages `H ⊓ K = ⊥` and `H ⊔ K = ⊤`) then no edge of `G` can have only one
endpoint in `H`.
-/
lemma Subgraph.mem_verts_iff_of_isCompl {H K : G.Subgraph} (h : IsCompl H K)
    {v w : V} (hadj : G.Adj v w) : v ∈ H.verts ↔ w ∈ H.verts := by
  -- The vertex sets of `H` and `K` are disjoint.
  have hdisj : Disjoint H.verts K.verts := by
    simpa [Set.disjoint_iff_inter_eq_empty] using
      congrArg Subgraph.verts h.inf_eq_bot
  -- The G-edge v — w lies in the sup, hence in `H` or `K`.
  have hsup : H.Adj v w ∨ K.Adj v w := Subgraph.sup_adj.1 (h.sup_eq_top ▸ hadj)
  -- In either case both endpoints lie on the same side of the partition.
  rcases hsup with hH | hK
  · exact ⟨fun _ => hH.snd_mem, fun _ => hH.fst_mem⟩
  · exact iff_of_false (hdisj.notMem_of_mem_right hK.fst_mem)
      (hdisj.notMem_of_mem_right hK.snd_mem)

/-!
2. Prove that the *Heyting complement* of a subgraph `H` (which is how `Hᶜ` is
defined) is `(⊤ : G.Subgraph).induce H.vertsᶜ`
-/
example (H : G.Subgraph) : Hᶜ = (⊤ : G.Subgraph).induce H.vertsᶜ := by
  -- We show `Hᶜ ≤ ⊤.induce H.vertsᶜ` and `⊤.induce H.vertsᶜ ≤ Hᶜ`.
  -- The key fact is `disjoint_compl_left : Disjoint Hᶜ H`, which forces every vertex
  -- and edge of `Hᶜ` to avoid `H`.
  have hdisj : Disjoint Hᶜ H := disjoint_compl_left
  have hverts : ∀ {v}, v ∈ Hᶜ.verts → v ∉ H.verts := fun {v} hvc hvH => by
    have : v ∈ (Hᶜ ⊓ H).verts := ⟨hvc, hvH⟩
    rw [disjoint_iff.mp hdisj] at this
    exact this
  apply le_antisymm
  · -- `Hᶜ ≤ ⊤.induce H.vertsᶜ`
    refine ⟨fun v hv => hverts hv, fun u v huv =>
      ⟨hverts huv.fst_mem, hverts huv.snd_mem, huv.adj_sub⟩⟩
  · -- `⊤.induce H.vertsᶜ ≤ Hᶜ`: it is disjoint from `H`,
    -- so lies below the Heyting complement.
    rw [le_compl_iff_disjoint_right]
    refine disjoint_iff_inf_le.mpr ⟨?_, ?_⟩
    · -- verts of the inf are ⊆ ⊥.verts = ∅
      rintro v ⟨hv, hvH⟩
      exact (hv hvH).elim
    · -- adjacencies of the inf imply ⊥.Adj
      rintro u v ⟨⟨hu, _, _⟩, hH⟩
      exact hu hH.fst_mem

/-!
3. Show that any edge of an induced subgraph is an edge of `G`.
-/
example (s : Set V) (v w : V) (h : ((⊤ : G.Subgraph).induce s).Adj v w) :
    G.Adj v w :=
  h.2.2.adj_sub

/-!
4. Show that the induced subgraph on `Set.univ` is the `top` subgraph.
-/
example : (⊤ : G.Subgraph).induce Set.univ = ⊤ := by
  ext <;> simp

/-!
5. Show that the single-edge subgraph `G.subgraphOfAdj hadj` is a subgraph of a
subgraph `H` if and only if `H` contains the edge.
-/
example {v w : V} (hadj : G.Adj v w) (H : G.Subgraph) :
    G.subgraphOfAdj hadj ≤ H ↔ H.Adj v w := subgraphOfAdj_le_iff _ _

/-!
6. Show that an induced subgraph `(⊤ : G.Subgraph).induce s` is induced (in the sense
of `Subgraph.IsInduced`).
-/
example (s : Set V) : ((⊤ : G.Subgraph).induce s).IsInduced :=
  -- Any two vertices of `s` adjacent in `G` are adjacent in the induced subgraph.
  fun _ hu _ hv hadj => ⟨hu, hv, hadj⟩

/-!
7. Show that the spanning coercion of a single vertex subgraph is the empty graph
`⊥ : SimpleGraph V`, which has *every* vertex of `V`. So `spanningCoe` forgets the
vertex set of a subgraph.
-/
example (v : V) : (G.singletonSubgraph v).spanningCoe = ⊥ := by
  ext a b
  simp

/-!
8. Show that if every induced subgraph of `G` on a finite set of vertices is
`n`-colourable then `G` is `n`-colourable. Hint: use the De Bruijn–Erdős theorem
`colorable_of_forall_finite_subgraph_colorable`. For a finite subgraph `H`, the graph
`H.coe` is a subgraph of `G.induce H.verts` on the same vertex type `↑H.verts`, so
`Colorable.mono_left` applies.
-/
lemma colorable_of_forall_finite_induce_colorable {n : ℕ}
    (h : ∀ s : Set V, s.Finite → (G.induce s).Colorable n) : G.Colorable n :=
  colorable_of_forall_finite_subgraph_colorable fun H hH =>
    -- `H.coe ≤ G.induce H.verts`: every edge of `H` is an edge of `G`.
    (h H.verts hH).mono_left (G := H.coe) fun _ _ hab => H.adj_sub hab

/-!
9. Show that the matching number is monotone: if `G ≤ H` then `ν G ≤ ν H`. Hint:
turn a matching of `G` into a matching of `H` with the same edges by building the
`H.Subgraph` directly, then use the `matchingNum` API (`matchingNum_le` and
`Subgraph.IsMatching.le_matchingNum`). (Mathlib's `Subgraph.IsMatching.map_ofLE`
says that `M.map (Hom.ofLE h)` is a matching of `H`, but its edges are then harder
to count.)
-/
lemma matchingNum_mono {G H : SimpleGraph V} (h : G ≤ H) :
    ν G ≤ ν H :=
  -- every matching of `G` is a matching of `H` with the same vertices and edges:
  -- only the `adj_sub` field needs updating, using `G ≤ H`
  matchingNum_le fun M hM => Subgraph.IsMatching.le_matchingNum
    (M := ⟨M.verts, M.Adj, fun hadj => h (M.adj_sub hadj), M.edge_vert, M.symm⟩) hM

/-!
10. Show that `ν K[3] = 1` but `τ K[3] = 2`, so weak duality `ν G ≤ τ G` can be
strict. Hint: for the first, `matchingNum_le_card_div_two` gives the upper bound and
a single edge is a matching (`Subgraph.IsMatching.subgraphOfAdj`). For the second,
use Mathlib's `vertexCoverNum_top`.
-/
example : ν K[3] = 1 := by
  refine le_antisymm ?_ ?_
  · -- `K[3]` has `3` vertices, so a matching has at most `3 / 2 = 1` edges.
    simpa using matchingNum_le_card_div_two (G := K[3])
  · -- The single edge `0 — 1` is a matching with one edge.
    have h : K[3].Adj 0 1 := by decide
    simpa using (Subgraph.IsMatching.subgraphOfAdj h).le_matchingNum

example : τ K[3] = 2 := by
  rw [vertexCoverNum_top, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  rfl

/-!
11. Show that the infinite path has matching number `⊤`. Hint: build the subgraph of
`pathNat₁` that pairs `2 * k` with `2 * k + 1`. (An easy way to define this adjacency
relation is as `pathNat₁.Adj m n ∧ m / 2 = n / 2`.) Show that it is a matching, and
show that its edge set is infinite (`Set.infinite_of_injective_forall_mem`).
-/
lemma matchingNum_pathNat₁ : ν pathNat₁ = ⊤ := by
  -- Pair `2 * k` with `2 * k + 1`.
  let M : pathNat₁.Subgraph :=
    { verts := Set.univ
      Adj m n := pathNat₁.Adj m n ∧ m / 2 = n / 2
      adj_sub h := h.1
      edge_vert _ := trivial
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩ }
  have hM : M.IsMatching := by
    intro v _
    refine ⟨if v % 2 = 0 then v + 1 else v - 1, ?_, ?_⟩
    · simp only [M]
      split_ifs <;> grind
    · rintro w ⟨hw, hw2⟩
      simp only at hw
      split_ifs <;> grind
  -- The edges `s(2 * k, 2 * k + 1)` are distinct edges of `M`.
  have hinf : M.edgeSet.Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => s(2 * k, 2 * k + 1)) (fun a b h => ?_) (fun k => ?_)
    · simp only [Sym2.eq_iff] at h
      grind
    · simp only [M, Subgraph.mem_edgeSet]
      grind
  exact top_le_iff.mp (hinf.encard_eq ▸ hM.le_matchingNum)

/-!
12. Show that in a finite graph `⍺ G + ν G ≤ |V|`. Hint: let `I` be a maximum
independent set (`exists_isNIndepSet_indepNum`) and `M` a maximum matching
(`exists_isMatching_matchingNum`), so `#I = ⍺ G` and `M` has `ν G` edges. Count the
vertices of `I` inside and outside `M.verts` separately:
* *Inside:* no edge of `M` has both ends in `I`, since `I` is independent. So
  sending each `v ∈ I ∩ M.verts` to the edge of `M` containing it is injective, and
  at most `|E(M)|` vertices of `I` lie in `M.verts`
  (`Subgraph.IsMatching.ncard_inter_le_of_isIndepSet`).
* *Outside:* `M.verts` has `2 * |E(M)|` vertices (`Subgraph.IsMatching.ncard_verts`),
  so at most `|V| - 2 * |E(M)|` vertices lie outside it.

Adding these gives `⍺ G ≤ |V| - |E(M)|`. To do the arithmetic in `ℕ`, write `ν G` as
the cast of `M.edgeSet.ncard` using `Set.coe_ncard_eq_encard`.
-/
lemma indepNum_add_matchingNum_le [Finite V] :
    (⍺ G : ℕ∞) + ν G ≤ Nat.card V := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨M, hM, hcard⟩ := exists_isMatching_matchingNum (G := G)
  -- Sending each vertex of `I` covered by `M` to its edge of `M` is injective
  -- (`IsMatching.ncard_inter_le_of_isIndepSet`).
  have h1 : (↑I ∩ M.verts).ncard ≤ M.edgeSet.ncard :=
    hM.ncard_inter_le_of_isIndepSet hI.isIndepSet
  -- The other vertices of `I` lie outside `M.verts`.
  have h2 : (↑I \ M.verts).ncard ≤ Nat.card V - 2 * M.edgeSet.ncard := by
    rw [← hM.ncard_verts, ← Set.ncard_univ, ← Set.ncard_sdiff (Set.subset_univ _)]
    exact Set.ncard_le_ncard (fun v hv => ⟨trivial, hv.2⟩)
  have h3 : I.card = (↑I ∩ M.verts).ncard + (↑I \ M.verts).ncard := by
    rw [Set.ncard_inter_add_ncard_sdiff_eq_ncard, Set.ncard_coe_finset]
  have h4 : 2 * M.edgeSet.ncard ≤ Nat.card V := by
    rw [← hM.ncard_verts]
    exact Set.ncard_le_card _
  rw [← hcard, ← Set.coe_ncard_eq_encard, ← hI.card_eq]
  norm_cast
  grind

/-!
13. Deduce that `⍺ Q[n + 1] ≤ 2 ^ n`. (In fact `⍺ Q[n + 1] = 2 ^ n`: the vertices
with an even number of `1`s form an independent set.)
-/
example (n : ℕ) : ⍺ Q[n + 1] ≤ 2 ^ n := by
  have h := indepNum_add_matchingNum_le (G := Q[n + 1])
  rw [hypercube.matchingNum_succ, Nat.card_eq_fintype_card, card_hypercubeVert,
    pow_succ, mul_two] at h
  have h' : ⍺ Q[n + 1] + 2 ^ n ≤ 2 ^ n + 2 ^ n := by exact_mod_cast h
  grind

/-!
14. The supremum of an increasing sequence of matchings is a matching. Hint: a
vertex of `⨆ n, M n` lies in some `M n` (`Subgraph.verts_iSup`) and an edge of
`⨆ n, M n` lies in some `M m` (`Subgraph.iSup_adj`); compare the two at the later
stage `max n m`.
-/
lemma Subgraph.IsMatching.iSup_of_monotone {M : ℕ → G.Subgraph}
    (hmono : Monotone M) (hM : ∀ n, (M n).IsMatching) : (⨆ n, M n).IsMatching := by
  intro v hv
  rw [Subgraph.verts_iSup, Set.mem_iUnion] at hv
  obtain ⟨n, hn⟩ := hv
  obtain ⟨w, hw, -⟩ := hM n hn
  refine ⟨w, Subgraph.iSup_adj.mpr ⟨n, hw⟩, fun w' hw' => ?_⟩
  obtain ⟨m, hm⟩ := Subgraph.iSup_adj.mp hw'
  -- Both edges are present at the later stage `max n m`, which is a matching.
  obtain ⟨u, -, hu⟩ := hM (max n m) ((hmono (le_max_left n m)).1 hn)
  rw [hu w' ((hmono (le_max_right n m)).2 hm),
    hu w ((hmono (le_max_left n m)).2 hw)]

/-!
15. If `ν G = ⊤` then every finite set of vertices `S` misses some edge of `G`.
Hint: otherwise `S` is a vertex cover, so weak duality
(`matchingNum_le_vertexCoverNum`) and `IsVertexCover.vertexCoverNum_le` force
`S.encard = ⊤`.
-/
lemma exists_adj_notMem_of_matchingNum_eq_top (h : ν G = ⊤) {S : Set V}
    (hS : S.Finite) : ∃ a b, G.Adj a b ∧ a ∉ S ∧ b ∉ S := by
  by_contra! hcon
  -- Otherwise `S` is a vertex cover, contradicting weak duality `ν G ≤ τ G`.
  have hcover : G.IsVertexCover S := by
    intro a b hab
    by_cases ha : a ∈ S
    · exact Or.inl ha
    · exact Or.inr (hcon a b hab ha)
  have := (G.matchingNum_le_vertexCoverNum).trans hcover.vertexCoverNum_le
  rw [h, top_le_iff, Set.encard_eq_top_iff] at this
  exact this hS

/-!
16. A matching `M` with finitely many vertices in a graph with `ν G = ⊤` can be
extended by one edge. Hint: take an edge avoiding `M.verts` from the previous
exercise and add it with `Subgraph.IsMatching.sup`, whose disjointness hypothesis
is about supports (`Subgraph.IsMatching.support_eq_verts`), then count edges with
`Set.encard_insert_of_notMem`.
-/
lemma Subgraph.IsMatching.exists_le_encard_eq_add_one (h : ν G = ⊤)
    {M : G.Subgraph} (hM : M.IsMatching) (hfin : M.verts.Finite) :
    ∃ N : G.Subgraph, M ≤ N ∧ N.IsMatching ∧ N.verts.Finite ∧
      N.edgeSet.encard = M.edgeSet.encard + 1 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_adj_notMem_of_matchingNum_eq_top h hfin
  refine ⟨M ⊔ G.subgraphOfAdj hab, le_sup_left, ?_, ?_, ?_⟩
  · -- The new edge avoids `M`, so the union is a matching.
    refine hM.sup (Subgraph.IsMatching.subgraphOfAdj hab) ?_
    rw [hM.support_eq_verts,
        (Subgraph.IsMatching.subgraphOfAdj hab).support_eq_verts,
        subgraphOfAdj_verts, Set.disjoint_left]
    rintro x hx (rfl | rfl)
    · exact ha hx
    · exact hb hx
  · rw [Subgraph.verts_sup, subgraphOfAdj_verts]
    exact hfin.union (Set.toFinite _)
  · rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton,
        Set.encard_insert_of_notMem]
    rw [Subgraph.mem_edgeSet]
    exact fun hadj => ha (M.edge_vert hadj)

/-!
17. If `ν G = ⊤` then `G` has an infinite matching. Hint: restate the previous
exercise on the subtype `FM := {M : G.Subgraph // M.IsMatching ∧ M.verts.Finite}`
of finite matchings, so that `choose` produces a step function `next : FM → FM`,
and iterate it from `⊥`: `M n := next^[n] ⊥`, with `Function.iterate_succ_apply'`
unfolding one step. Each `M n` is then a finite matching by construction; show by
induction that it has exactly `n` edges. Each step extends the previous matching, so
`M` is monotone (`monotone_nat_of_le_succ`) and `⨆ n, M n` is a matching by
Exercise 14 with at least `n` edges for every `n`.
-/
lemma exists_isMatching_encard_eq_top (h : ν G = ⊤) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = ⊤ := by
  -- Choose, for every finite matching, an extension by one edge. Packaging the
  -- finite matchings as a subtype `FM` makes this a total function `next`.
  let FM := {M : G.Subgraph // M.IsMatching ∧ M.verts.Finite}
  have : ∀ M : FM, ∃ N : FM,
      M.1 ≤ N.1 ∧ N.1.edgeSet.encard = M.1.edgeSet.encard + 1 := by
    rintro ⟨M, hM, hfin⟩
    obtain ⟨N, hle, hN, hNfin, hcard⟩ := hM.exists_le_encard_eq_add_one h hfin
    exact ⟨⟨N, hN, hNfin⟩, hle, hcard⟩
  choose next hnext hcard using this
  -- Iterate from the empty matching.
  let M : ℕ → FM := fun n => next^[n] ⟨⊥, Subgraph.isMatching_bot, by simp⟩
  have hstep : ∀ n, M (n + 1) = next (M n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  -- Each `M n` is a finite matching by construction; it has exactly `n` edges.
  have hcount : ∀ n : ℕ, (M n).1.edgeSet.encard = n := by
    intro n
    induction n with
    | zero => simp [M]
    | succ n ih => rw [hstep, hcard, ih, Nat.cast_succ]
  have hmono : Monotone fun n => (M n).1 := monotone_nat_of_le_succ fun n => by
    rw [hstep]
    exact hnext (M n)
  refine ⟨⨆ n, (M n).1,
    Subgraph.IsMatching.iSup_of_monotone hmono fun n => (M n).2.1, ?_⟩
  -- The union contains a matching with `n` edges for every `n`, so it is infinite.
  have hle : ∀ n : ℕ, (n : ℕ∞) ≤ (⨆ n, (M n).1).edgeSet.encard := fun n => by
    rw [← hcount n]
    exact Set.encard_le_encard <| Subgraph.edgeSet_mono <| le_iSup_of_le n le_rfl
  exact ENat.eq_top_iff_forall_ge.2 hle

/-!
18. Conclude that the matching number is attained in every graph, finite or not:
this is the analogue of Mathlib's `vertexCoverNum_exists`. Hint: if `ν G = ⊤` use
the previous exercise; otherwise a finite supremum in `ℕ∞` is attained
(`ENat.exists_eq_iSup_of_lt_top`), exactly as in the proof of
`exists_isMatching_matchingNum`.
-/
lemma matchingNum_exists (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = ν G := by
  by_cases htop : ν G = ⊤
  · obtain ⟨M, hM, hcard⟩ := exists_isMatching_encard_eq_top htop
    exact ⟨M, hM, hcard.trans htop.symm⟩
  · -- A finite supremum in `ℕ∞` is attained.
    have : Nonempty {M : G.Subgraph // M.IsMatching} :=
      ⟨⟨⊥, Subgraph.isMatching_bot⟩⟩
    obtain ⟨M, hM⟩ := ENat.exists_eq_iSup_of_lt_top
      (f := fun x : {M : G.Subgraph // M.IsMatching} =>
        (x : G.Subgraph).edgeSet.encard)
      (by rw [← matchingNum_eq_iSup_subtype]; exact lt_top_iff_ne_top.mpr htop)
    exact ⟨M, M.2, by rw [matchingNum_eq_iSup_subtype]; exact hM⟩

/-!
19. Show that, provided there is at least one colour, `s` is `n`-colourable in the
sense of `ColorableOn` iff the induced subgraph `G.induce s` is `n`-colourable. (So
partial colourings really do capture colourings of induced subgraphs.) Why is the
hypothesis `0 < n` needed?
-/
lemma colorableOn_iff_colorable_induce {n : ℕ} (hn : 0 < n) (s : Set V) :
    G.ColorableOn n s ↔ (G.induce s).Colorable n := by
  classical
  constructor
  · -- Restrict the colouring to `s`.
    rintro ⟨C⟩
    exact ⟨Coloring.mk (fun v => C v) fun {v w} h => C.valid ⟨v.2, w.2, h⟩⟩
  · -- Colour the vertices outside `s` with colour `0`. (If `n = 0` and `V` is
    -- nonempty there is no such colour, although `G.induce ∅` is `0`-colourable.)
    rintro ⟨c⟩
    refine ⟨Coloring.mk (fun v => if hv : v ∈ s then c ⟨v, hv⟩ else ⟨0, hn⟩) ?_⟩
    rintro v w ⟨hv, hw, hadj⟩
    simp only [hv, hw, ↓reduceDIte]
    exact c.valid (by simpa using hadj)

/-! END SOLUTIONS -/


end SimpleGraph
