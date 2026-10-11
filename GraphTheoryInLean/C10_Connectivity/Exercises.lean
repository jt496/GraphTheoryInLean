import GraphTheoryInLean.C10_Connectivity.C10_Connectivity
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
open Walk
/-!
# Exercises

1. Show that for any graph `G` on a nonempty vertex type, either `G` or its
complement `Gᶜ` is connected. Hint: if `u` and `v` are not reachable from each other
in `G`, show that any two vertices are joined in `Gᶜ`, either directly or through `u`
or `v`. (Mathlib has this as `connected_or_connected_compl`, but try to prove it
directly.)
-/
example [Nonempty V] : G.Connected ∨ Gᶜ.Connected := by
  sorry

/-!
2. Show that the complete bipartite graph `K[s + 1, t + 1]` is connected.
-/
example (s t : ℕ) : K[s + 1, t + 1].Connected := by
  sorry

/-!
3. Construct the equivalence between the connected components of the empty graph and
its vertex type. Hint: `ConnectedComponent.lift` and `ConnectedComponent.ind`; what
does a walk in `⊥` look like?
-/
def botComponentEquiv' (V : Type*) : (⊥ : SimpleGraph V).ConnectedComponent ≃ V :=
  sorry

/-!
4. Prove the universal property of the disjoint union: a family of homomorphisms
`G i →g H` into a common graph `H` gives a homomorphism `Σg G →g H`. Hint: adjacent
vertices of the disjoint union have the same index.
-/
def Hom.sigmaDesc' {ι : Type*} {V : ι → Type*} {W : Type*}
    (G : (i : ι) → SimpleGraph (V i))
    {H : SimpleGraph W} (f : (i : ι) → G i →g H) : SimpleGraph.sigma G →g H :=
  sorry

/-!
5. Use the previous exercise and `isoSigmaConnectedComponents` to build a
homomorphism `G →g H` from a homomorphism out of each connected component of `G`.
(Mathlib provides this map as `SimpleGraph.homOfConnectedComponents`.)
-/
example {W : Type*} {H : SimpleGraph W}
    (f : (C : G.ConnectedComponent) → C.toSimpleGraph →g H) : G →g H :=
  sorry

/-!
6. Show that if `G` has no isolated vertices then the Mycielskian `mμ[G]` has no
bridges. Hint: `isBridge_mycielskian_iff`.
-/
example (hG : ∀ v, ¬ G.IsIsolated v) {e : Sym2 (Option (V ⊕ V))}
    (he : e ∈ mμ[G].edgeSet) : ¬ mμ[G].IsBridge e := by
  sorry

/-!
7. Show that the path graph `pathGraph (n + 1)` is a tree. Hint: deduce acyclicity
from `pathNat₁_isAcyclic` using `IsAcyclic.comap`.
-/
example (n : ℕ) : P[n + 1].IsTree := by
  sorry

/-!
8. Show that a tree has at most one connected component.
-/
example (h : G.IsTree) : Subsingleton G.ConnectedComponent := by
  sorry

/-!
9. Show that a finite tree has at least as many leaves (vertices of degree one) as
the degree of any of its vertices. Hint: every vertex `u ≠ v` has degree at least
one, so `degree u + (if G.degree u = 1 then 1 else 0)` is at least 2. Sum this over
all vertices and compare with the Handshaking Lemma
(`sum_degrees_eq_twice_card_edges`) and `IsTree.card_edgeFinset`.
-/
open Finset in
lemma IsTree.degree_le_card_leaves' [Fintype V] [DecidableRel G.Adj] (h : G.IsTree)
    (v : V) : G.degree v ≤ #{u | G.degree u = 1} := by
  sorry

/-!
10. Show that every finite connected graph with at least two vertices has a vertex
whose deletion leaves it connected (so not every vertex is a cut vertex). Hint: take
a leaf `v` of a spanning tree `T` (`IsTree.exists_vert_degree_one_of_nontrivial`).
Deleting it leaves `T` connected
(`Connected.induce_compl_singleton_of_degree_eq_one`), and `Connected.mono` transfers
this to `G`.
-/
example [Finite V] [Nontrivial V] (h : G.Connected) :
    ∃ v, (G.induce {v}ᶜ).Connected := by
  sorry

/-!
11. Show that deleting a leaf (a vertex of degree one) from a tree leaves a tree.
Hint: search Mathlib (see
[Finding Lemmas](https://jt496.github.io/GraphTheoryInLean/Introduction/#section-finding-lemmas))
for a lemma about `induce` and a vertex of degree one.
-/
example [G.LocallyFinite] (hT : G.IsTree) {v : V}
    (hv : G.degree v = 1) : (G.induce {v}ᶜ).IsTree := by
  sorry

/-!
12. Strengthen `Walk.exists_odd_isCycle`: a closed walk of odd length `k` contains a
cycle of odd length at most `k`. Hint: first strengthen
`Walk.exists_isPath_or_odd_isCycle` so that the path and the cycle it produces are
no longer than the original walk, then follow the proof of `Walk.exists_odd_isCycle`.
-/
theorem Walk.exists_odd_isCycle_length_le' {u : V} (w : G.Walk u u)
    (hw : Odd w.length) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧ c.length ≤ w.length := by
  sorry

/-!
13. Use Euler's theorem (`Connected.exists_isEulerian_circuit`) to show that
the complete graph on an odd number of vertices has an Eulerian circuit, and so does
the hypercube `Q[2 * n + 2]`.
-/
example (n : ℕ) : ∃ u, ∃ p : K[2 * n + 3].Walk u u, p.IsEulerian := by
  sorry

example (n : ℕ) : ∃ u, ∃ p : Q[2 * n + 2].Walk u u, p.IsEulerian := by
  sorry

/-!
14. Show that the hypercube `Q[n + 2]` has no bridges. Hint: `Q[n + 2]` is
`2`-edge-connected by `hypercube_isEdgeConnected` and `IsEdgeConnected.anti`; now use
`isBridge_iff_not_isEdgeReachable_two`.
-/
example (n : ℕ) {u v : HypercubeVert (n + 2)} (h : Q[n + 2].Adj u v) :
    ¬ Q[n + 2].IsBridge s(u, v) := by
  sorry

/-!
15. Show that a `k`-vertex-connected graph has minimum degree at least `k`. Hint:
`IsVertexConnected.le_degree` and `le_minDegree_of_forall_le_degree`.
-/
lemma IsVertexConnected.le_minDegree' {k : ℕ} [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] (hG : G.IsVertexConnected k) : k ≤ G.minDegree := by
  sorry

/-!
16. Show that the edge connectivity of a finite graph with at least two vertices is
at most its minimum degree. Together with `vertexConnectivity_le_edgeConnectivity`
this gives Whitney's inequalities `κ(G) ≤ λ(G) ≤ δ(G)`. Hint:
`exists_minimal_degree_vertex` and `edgeConnectivity_le_degree`.
-/
lemma edgeConnectivity_le_minDegree' [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : λ(G) ≤ G.minDegree := by
  sorry

/-!
17. The *bowtie* consists of two triangles `0, 1, 2` and `0, 3, 4` sharing the vertex
`0`. Instance search does not unfold the definition of `bowtie`, so we supply its
`DecidableRel` instance by hand; this lets `decide` check properties of the bowtie.
-/
/-- The *bowtie*: two triangles `0, 1, 2` and `0, 3, 4` sharing the vertex `0`. -/
def bowtie : SimpleGraph (Fin 5) :=
  fromRel fun i j => (i, j) ∈ [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]

instance : DecidableRel bowtie.Adj := inferInstanceAs (DecidableRel (fromRel _).Adj)

/-!
Show that `κ(bowtie) < λ(bowtie)`, so the first of Whitney's inequalities can be
strict. Hint: the bowtie is `2`-edge-connected by `isEdgeConnected_two` and
`decide`. It is not `2`-vertex-connected, by `isVertexConnected_iff_induce` with
`S = {0}` and `decide`. Finally use `le_edgeConnectivity_iff` and
`le_vertexConnectivity_iff`.
-/
example : κ(bowtie) < λ(bowtie) := by
  sorry

/-!
18. Show that the vertex connectivity of the hypercube `Q[n]` is exactly `n`. Hint:
the lower bound is `hypercube_isVertexConnected` (via `le_vertexConnectivity_iff`);
for the upper bound use `vertexConnectivity_le_encard_neighborSet` at any vertex,
together with `hypercube_isRegularOfDegree`.
-/
lemma hypercube_vertexConnectivity' (n : ℕ) : κ(Q[n]) = n := by
  sorry

/-!
19. Show that the edge connectivity of `Q[n + 1]` is `n + 1`, but that the edge
connectivity of `Q[0]` is `⊤`. Hint: use `vertexConnectivity_le_edgeConnectivity` and
`edgeConnectivity_le_degree`, which needs a `Nontrivial (HypercubeVert (n + 1))`
instance, and `edgeConnectivity_of_subsingleton`. Instance search deliberately does
not see through `HypercubeVert`, so you will have to supply these instances yourself,
for example with `inferInstanceAs (Nontrivial (HypercubeVert n × Bool))`.
-/
lemma hypercube_edgeConnectivity' (n : ℕ) : λ(Q[n + 1]) = n + 1 := by
  sorry

lemma hypercube_zero_edgeConnectivity' : λ(Q[0]) = ⊤ := by
  sorry

/-!
20. Show that in a forest the block of an edge `e` consists of the single edge `e`.
Hint: show that block-equivalent edges of a forest are equal, by induction on
`BlockEquivalent`.
-/
lemma IsAcyclic.blockOf_eq' (hG : G.IsAcyclic) (e : Sym2 V) :
    G.blockOf e = fromEdgeSet {e} := by
  sorry

/-!
21. Show that for `n ≥ 1` a graph is `n`-colourable iff each of its blocks is. Hint:
the forward direction follows from `blockOf_le`. For the reverse direction use the De
Bruijn–Erdős theorem (`colorable_of_forall_finite_subgraph_colorable`) to reduce to a
finite subgraph `H`, which is colourable by `colorable_of_forall_block` provided its
blocks are. Each block of `H` maps into a block of `G` via `blockOfHom` applied to
`H.hom`.
-/
theorem colorable_iff_forall_block' {n : ℕ} (hn : 1 ≤ n) :
    G.Colorable n ↔ ∀ B : G.Block, B.toGraph.Colorable n := by
  sorry

/-! SOLUTIONS -/

/-!
1. Show that for any graph `G` on a nonempty vertex type, either `G` or its
complement `Gᶜ` is connected. Hint: if `u` and `v` are not reachable from each other
in `G`, show that any two vertices are joined in `Gᶜ`, either directly or through `u`
or `v`. (Mathlib has this as `connected_or_connected_compl`, but try to prove it
directly.)

If `G` is not preconnected, pick vertices `u` and `v` that are not reachable from
each other. Vertices `x` and `y` that are not reachable from each other in `G` are
distinct and not adjacent, so they are adjacent in `Gᶜ`. If `x` and `y` are reachable
from each other in `G`, then they lie in a component of `G` that misses `u` or `v`,
and both are adjacent in `Gᶜ` to whichever of these it misses.
-/
example [Nonempty V] : G.Connected ∨ Gᶜ.Connected := by
  by_cases hG : G.Preconnected
  · exact .inl ⟨hG⟩
  -- otherwise some pair `u`, `v` is not reachable in `G`
  simp only [Preconnected, not_forall] at hG
  obtain ⟨u, v, huv⟩ := hG
  -- vertices that are not reachable from each other in `G` are adjacent in `Gᶜ`
  have hadj (x y : V) (h : ¬ G.Reachable x y) : Gᶜ.Adj x y :=
    ⟨fun hxy => h (hxy ▸ .refl _), fun hxy => h hxy.reachable⟩
  refine .inr ⟨fun x y => ?_⟩
  by_cases hxy : G.Reachable x y
  · -- `x` and `y` lie in one component of `G`, which misses `u` or `v`
    by_cases hxu : G.Reachable x u
    · have hxv : ¬ G.Reachable x v := fun h => huv (hxu.symm.trans h)
      have hyv : ¬ G.Reachable y v := fun h => hxv (hxy.trans h)
      exact (hadj x v hxv).reachable.trans (hadj y v hyv).reachable.symm
    · have hyu : ¬ G.Reachable y u := fun h => hxu (hxy.trans h)
      exact (hadj x u hxu).reachable.trans (hadj y u hyu).reachable.symm
  · exact (hadj x y hxy).reachable

/-!
2. Show that the complete bipartite graph `K[s + 1, t + 1]` is connected.
-/
example (s t : ℕ) : K[s + 1, t + 1].Connected := by
  apply (connected_iff_exists_forall_reachable _).2 ⟨.inl 0, fun v => ?_⟩
  match v with
  | .inl b =>
    have h : K[s + 1, t + 1].Adj (.inl 0) (.inr 0) := by simp
    use (.cons h <| .cons (by simp) .nil)
  | .inr b =>
    exact (by simp : K[s + 1, t + 1].Adj (.inl 0) (.inr b)).reachable

/-!
3. Construct the equivalence between the connected components of the empty graph and
its vertex type. Hint: `ConnectedComponent.lift` and `ConnectedComponent.ind`; what
does a walk in `⊥` look like?

Any walk in `⊥` is `nil`, so reachability in `⊥` is equality and
`connectedComponentMk` is a bijection.
-/
def botComponentEquiv (V : Type*) : (⊥ : SimpleGraph V).ConnectedComponent ≃ V where
  toFun := ConnectedComponent.lift id fun v w p _ => by
    cases p with
    | nil => rfl
    | cons h _ => exact h.elim
  invFun := (⊥ : SimpleGraph V).connectedComponentMk
  left_inv := ConnectedComponent.ind fun v => rfl
  right_inv v := rfl

/-!
4. Prove the universal property of the disjoint union: a family of homomorphisms
`G i →g H` into a common graph `H` gives a homomorphism `Σg G →g H`. Hint: adjacent
vertices of the disjoint union have the same index.

An edge `⟨i, u⟩ — ⟨i, v⟩` of the disjoint union is an edge of `G i`, which `f i`
preserves.
-/
/-- The universal property of the disjoint union: a family of homomorphisms
`G i →g H` into a common graph descends to a single homomorphism `Σg G →g H` out of
the coproduct. -/
def Hom.sigmaDesc {ι : Type*} {V : ι → Type*} {W : Type*}
    (G : (i : ι) → SimpleGraph (V i))
    {H : SimpleGraph W} (f : (i : ι) → G i →g H) : SimpleGraph.sigma G →g H where
  toFun p := f p.1 p.2
  map_rel' := by
    rintro ⟨i, u⟩ ⟨j, v⟩ ⟨rfl, hadj⟩
    exact (f i).map_rel' hadj

/-!
5. Use the previous exercise and `isoSigmaConnectedComponents` to build a
homomorphism `G →g H` from a homomorphism out of each connected component of `G`.
(Mathlib provides this map as `SimpleGraph.homOfConnectedComponents`.)

We transport the homomorphism out of the disjoint union of the components along the
isomorphism `isoSigmaConnectedComponents`: each vertex is sent via the homomorphism
of its own component.
-/
example {W : Type*} {H : SimpleGraph W}
    (f : (C : G.ConnectedComponent) → C.toSimpleGraph →g H) : G →g H :=
  (Hom.sigmaDesc _ f).comp isoSigmaConnectedComponents.toHom

/-!
6. Show that if `G` has no isolated vertices then the Mycielskian `mμ[G]` has no
bridges. Hint: `isBridge_mycielskian_iff`.
-/
example (hG : ∀ v, ¬ G.IsIsolated v) {e : Sym2 (Option (V ⊕ V))}
    (he : e ∈ mμ[G].edgeSet) : ¬ mμ[G].IsBridge e := fun hb => by
  obtain ⟨u, hu, -⟩ := (isBridge_mycielskian_iff he).mp hb
  exact hG u hu

/-!
7. Show that the path graph `pathGraph (n + 1)` is a tree. Hint: deduce acyclicity
from `pathNat₁_isAcyclic` using `IsAcyclic.comap`.

The path graph is connected, and `Fin.val` is an injective homomorphism from
`P[n + 1]` into the infinite path `pathNat₁`, which is acyclic. So any cycle in
`P[n + 1]` would map to a cycle in `pathNat₁`.
-/
example (n : ℕ) : P[n + 1].IsTree :=
  ⟨pathGraph_connected n,
    pathNat₁_isAcyclic.comap ⟨Fin.val, by grind [pathGraph_adj]⟩ Fin.val_injective⟩

/-!
We can also prove that the path graph is a tree by showing that it has the correct
number of edges (`isTree_iff_connected_and_card`).
-/
example (n : ℕ) : P[n + 1].IsTree := by
  apply isTree_iff_connected_and_card.2 ⟨pathGraph_connected _,?_⟩
  simp only [Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin,
            Nat.add_right_cancel_iff]
  -- show `(P[n + 1]).edgeFinset.card = n` by exhibiting a bijection from `Fin n`
  have he : (P[n + 1]).edgeFinset = Finset.univ.image
      (fun i : Fin n ↦ s(⟨i.val, by grind⟩, ⟨i.val + 1, by grind⟩)) := by
    ext e
    refine e.ind fun a b ↦ ?_
    simp only [mem_edgeFinset, mem_edgeSet, pathGraph_adj, Finset.mem_image,
                Sym2.eq, Sym2.rel_iff',  Prod.swap_prod_mk]
    constructor
    · rintro (h | h)
      · exact ⟨⟨a.val, by grind⟩, by grind⟩
      · exact ⟨⟨b.val, by grind⟩, by grind⟩
    · grind
  rw [he, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  grind

/-!
8. Show that a tree has at most one connected component.
-/
example (h : G.IsTree) : Subsingleton G.ConnectedComponent :=
  h.connected.preconnected.subsingleton_connectedComponent

/-!
9. Show that a finite tree has at least as many leaves (vertices of degree one) as
the degree of any of its vertices. Hint: every vertex `u ≠ v` has degree at least
one, so `degree u + (if G.degree u = 1 then 1 else 0)` is at least 2. Sum this over
all vertices and compare with the Handshaking Lemma
(`sum_degrees_eq_twice_card_edges`) and `IsTree.card_edgeFinset`.

Note that no lower bound on the number of vertices is needed. (Mathlib has the
existence of one leaf in a nontrivial tree,
`IsTree.exists_vert_degree_one_of_nontrivial`, and of two distinct leaves,
`IsTree.exists_ne_and_degree_eq_one`, but not this count.)
-/
open Finset in
lemma IsTree.degree_le_card_leaves [Fintype V] [DecidableRel G.Adj] (h : G.IsTree)
    (v : V) : G.degree v ≤ #{u | G.degree u = 1} := by
  classical
  -- each vertex `u ≠ v` has degree ≥ 1, so its degree plus leaf indicator is ≥ 2
  have hge : ∀ u ∈ univ.erase v,
      2 ≤ G.degree u + if G.degree u = 1 then 1 else 0 := by
    intro u hu
    have : Nontrivial V := ⟨u, v, ne_of_mem_erase hu⟩
    have := h.connected.preconnected.minDegree_pos_of_nontrivial
    have := G.minDegree_le_degree u
    split_ifs <;> grind
  have hsum := sum_le_sum hge
  rw [sum_const, card_erase_of_mem (mem_univ v), card_univ, smul_eq_mul] at hsum
  -- split off `v` from the full sum, which is `2 * #edges + #leaves`
  have hsplit := add_sum_erase univ
    (fun u => G.degree u + if G.degree u = 1 then 1 else 0) (mem_univ v)
  have htot : ∑ u, (G.degree u + if G.degree u = 1 then 1 else 0)
      = 2 * #G.edgeFinset + #{u | G.degree u = 1} := by
    rw [sum_add_distrib, G.sum_degrees_eq_twice_card_edges, card_filter]
  have hcard := h.card_edgeFinset
  grind

/-!
10. Show that every finite connected graph with at least two vertices has a vertex
whose deletion leaves it connected (so not every vertex is a cut vertex). Hint: take
a leaf `v` of a spanning tree `T` (`IsTree.exists_vert_degree_one_of_nontrivial`).
Deleting it leaves `T` connected
(`Connected.induce_compl_singleton_of_degree_eq_one`), and `Connected.mono` transfers
this to `G`.

Mathlib has this result as
`Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`.
-/
example [Finite V] [Nontrivial V] (h : G.Connected) :
    ∃ v, (G.induce {v}ᶜ).Connected := by
  classical
  have := Fintype.ofFinite V
  -- a spanning tree `T` of `G` has a leaf `v`
  obtain ⟨T, hTG, hT⟩ := h.exists_isTree_le
  obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
  -- deleting a leaf keeps `T` connected, and `T.induce {v}ᶜ ≤ G.induce {v}ᶜ`
  exact ⟨v, (hT.connected.induce_compl_singleton_of_degree_eq_one hv).mono
    fun _ _ h => hTG h⟩

/-!
11. Show that deleting a leaf (a vertex of degree one) from a tree leaves a tree.
-/
example [G.LocallyFinite] (hT : G.IsTree) {v : V}
    (hv : G.degree v = 1) : (G.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv, hT.isAcyclic.induce _⟩

/-!
12. Strengthen `Walk.exists_odd_isCycle`: a closed walk of odd length `k` contains a
cycle of odd length at most `k`. Hint: first strengthen
`Walk.exists_isPath_or_odd_isCycle` so that the path and the cycle it produces are
no longer than the original walk, then follow the proof of `Walk.exists_odd_isCycle`.

The proof of `Walk.exists_isPath_or_odd_isCycle` goes through unchanged, carrying the
length bounds along: at each step the new path or cycle consists of part of the old
path together with at most one new edge, which is also the one new edge of the walk.
-/
lemma Walk.exists_isPath_or_odd_isCycle_le {a b : V} (p : G.Walk a b) :
    (∃ q : G.Walk a b, q.IsPath ∧ (Even q.length ↔ Even p.length) ∧
        q.length ≤ p.length) ∨
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧
        c.length ≤ p.length := by
  classical
  induction p with
  | nil => exact .inl ⟨nil, .nil, Iff.rfl, le_rfl⟩
  | @cons a _ _ h p ih =>
    rcases ih with ⟨q, hq, hpar, hle⟩ | ⟨v, c, hc, hodd, hle⟩
    · by_cases ha : a ∈ q.support
      · have hlen := congrArg length (q.take_spec ha)
        rw [length_append] at hlen
        rcases Nat.even_or_odd (q.takeUntil a ha).length with he | ho
        · exact .inr ⟨a, cons h (q.takeUntil a ha),
            (cons_isCycle_iff_length_ne_one _ h).mpr ⟨hq.takeUntil ha, by grind⟩,
            by grind [length_cons], by grind [length_cons]⟩
        · exact .inl ⟨q.dropUntil a ha, hq.dropUntil ha, by grind [length_cons],
            by grind [length_cons]⟩
      · exact .inl ⟨cons h q, hq.cons ha, by grind [length_cons],
          by grind [length_cons]⟩
    · exact .inr ⟨v, c, hc, hodd, by grind [length_cons]⟩

theorem Walk.exists_odd_isCycle_length_le {u : V} (w : G.Walk u u)
    (hw : Odd w.length) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧ c.length ≤ w.length := by
  cases w with
  | nil => simp at hw
  | cons h p =>
    rcases p.exists_isPath_or_odd_isCycle_le with
      ⟨q, hq, hpar, hle⟩ | ⟨v, c, hc, hodd, hle⟩
    · have hqe : Even q.length := by grind [length_cons]
      exact ⟨_, cons h q, (cons_isCycle_iff_length_ne_one _ h).mpr ⟨hq, by grind⟩,
        by grind [length_cons], by grind [length_cons]⟩
    · exact ⟨v, c, hc, hodd, by grind [length_cons]⟩

/-!
13. Use Euler's theorem (`Connected.exists_isEulerian_circuit`) to show that
the complete graph on an odd number of vertices has an Eulerian circuit, and so does
the hypercube `Q[2 * n + 2]`.

Both graphs are connected with all degrees even, so Euler's theorem applies directly.
-/
example (n : ℕ) : ∃ u, ∃ p : K[2 * n + 3].Walk u u, p.IsEulerian := by
  apply Connected.exists_isEulerian_circuit
  · exact connected_top_iff.mpr inferInstance
  · intro v
    have : (⊤ : SimpleGraph (Fin (2 * n + 3))).degree v = 2 * n + 2 := by
      simp [complete_graph_degree]
    rw [this]
    exact ⟨n + 1, by grind⟩

example (n : ℕ) : ∃ u, ∃ p : Q[2 * n + 2].Walk u u, p.IsEulerian :=
  (hypercube_connected _).exists_isEulerian_circuit fun v => by
    rw [hypercube_isRegularOfDegree]
    exact ⟨n + 1, by grind⟩

/-!
14. Show that the hypercube `Q[n + 2]` has no bridges. Hint: `Q[n + 2]` is
`2`-edge-connected by `hypercube_isEdgeConnected` and `IsEdgeConnected.anti`; now use
`isBridge_iff_not_isEdgeReachable_two`.
-/
example (n : ℕ) {u v : HypercubeVert (n + 2)} (h : Q[n + 2].Adj u v) :
    ¬ Q[n + 2].IsBridge s(u, v) := fun hb =>
  (isBridge_iff_not_isEdgeReachable_two h).mp hb
    ((hypercube_isEdgeConnected (n := n + 2)).anti (by grind) u v)

/-!
15. Show that a `k`-vertex-connected graph has minimum degree at least `k`. Hint:
`IsVertexConnected.le_degree` and `le_minDegree_of_forall_le_degree`.
-/
lemma IsVertexConnected.le_minDegree {k : ℕ} [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] (hG : G.IsVertexConnected k) : k ≤ G.minDegree :=
  G.le_minDegree_of_forall_le_degree k fun v => hG.le_degree v

/-!
16. Show that the edge connectivity of a finite graph with at least two vertices is
at most its minimum degree. Together with `vertexConnectivity_le_edgeConnectivity`
this gives Whitney's inequalities `κ(G) ≤ λ(G) ≤ δ(G)`. Hint:
`exists_minimal_degree_vertex` and `edgeConnectivity_le_degree`.
-/
lemma edgeConnectivity_le_minDegree [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : λ(G) ≤ G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact edgeConnectivity_le_degree v

/-!
17. Show that `κ(bowtie) < λ(bowtie)`, so the first of Whitney's inequalities can be
strict. Hint: the bowtie is `2`-edge-connected by `isEdgeConnected_two` and
`decide`. It is not `2`-vertex-connected, by `isVertexConnected_iff_induce` with
`S = {0}` and `decide`. Finally use `le_edgeConnectivity_iff` and
`le_vertexConnectivity_iff`.

In fact `κ(bowtie) = 1` and `λ(bowtie) = 2`, the minimum degree.
-/
example : κ(bowtie) < λ(bowtie) := by
  -- deleting any single edge leaves the bowtie preconnected
  have h2e : bowtie.IsEdgeConnected 2 := isEdgeConnected_two.mpr (by decide)
  -- deleting the shared vertex `0` disconnects it
  have h2v : ¬ bowtie.IsVertexConnected 2 := fun h =>
    absurd ((isVertexConnected_iff_induce.mp h).2 {0} (by simp)) (by decide)
  have hκ : κ(bowtie) < (2 : ℕ) := not_le.mp (mt le_vertexConnectivity_iff.mp h2v)
  exact hκ.trans_le (le_edgeConnectivity_iff.mpr h2e)

/-!
18. Show that the vertex connectivity of the hypercube `Q[n]` is exactly `n`. Hint:
the lower bound is `hypercube_isVertexConnected` (via `le_vertexConnectivity_iff`);
for the upper bound use `vertexConnectivity_le_encard_neighborSet` at any vertex,
together with `hypercube_isRegularOfDegree`.

The lower bound is `n`-vertex-connectivity of `Q[n]`, and the upper bound is the
degree `n` of any vertex.
-/
lemma hypercube_vertexConnectivity (n : ℕ) : κ(Q[n]) = n := by
  obtain ⟨v⟩ : Nonempty (HypercubeVert n) := inferInstance
  refine le_antisymm ((vertexConnectivity_le_encard_neighborSet v).trans_eq ?_)
    (le_vertexConnectivity_iff.mpr hypercube_isVertexConnected)
  rw [← coe_neighborFinset, Set.encard_coe_eq_coe_finsetCard,
    card_neighborFinset_eq_degree, hypercube_isRegularOfDegree n v]

/-!
19. Show that the edge connectivity of `Q[n + 1]` is `n + 1`, but that the edge
connectivity of `Q[0]` is `⊤`. Hint: use `vertexConnectivity_le_edgeConnectivity` and
`edgeConnectivity_le_degree`, which needs a `Nontrivial (HypercubeVert (n + 1))`
instance, and `edgeConnectivity_of_subsingleton`. Instance search deliberately does
not see through `HypercubeVert`, so you will have to supply these instances yourself,
for example with `inferInstanceAs (Nontrivial (HypercubeVert n × Bool))`.

For `Q[n + 1]` we have `n + 1 = κ(Q[n + 1]) ≤ λ(Q[n + 1])`, and `λ(Q[n + 1])` is at
most the degree `n + 1` of any vertex, since `Q[n + 1]` has at least two vertices.
The graph `Q[0]` has a single vertex, and Mathlib's `IsEdgeConnected k` has no
condition on the number of vertices, so `Q[0]` is `k`-edge-connected for every `k`.
-/
lemma hypercube_edgeConnectivity (n : ℕ) : λ(Q[n + 1]) = n + 1 := by
  have : Nontrivial (HypercubeVert (n + 1)) :=
    inferInstanceAs (Nontrivial (HypercubeVert n × Bool))
  obtain ⟨v⟩ : Nonempty (HypercubeVert (n + 1)) := inferInstance
  refine le_antisymm ((edgeConnectivity_le_degree v).trans_eq ?_) ?_
  · rw [hypercube_isRegularOfDegree (n + 1) v]; rfl
  · exact_mod_cast (hypercube_vertexConnectivity (n + 1)).symm.le.trans
      vertexConnectivity_le_edgeConnectivity

lemma hypercube_zero_edgeConnectivity : λ(Q[0]) = ⊤ :=
  have : Subsingleton (HypercubeVert 0) := inferInstanceAs (Subsingleton Unit)
  edgeConnectivity_of_subsingleton

/-!
20. Show that in a forest the block of an edge `e` consists of the single edge `e`.
Hint: show that block-equivalent edges of a forest are equal, by induction on
`BlockEquivalent`.

Two distinct edges of a forest never lie on a common cycle, so cycle-equivalence, and
hence block-equivalence, is just equality.
-/
lemma IsAcyclic.blockOf_eq (hG : G.IsAcyclic) (e : Sym2 V) :
    G.blockOf e = fromEdgeSet {e} := by
  -- block-equivalent edges of a forest are equal
  have key {f g : Sym2 V} (h : G.BlockEquivalent f g) : f = g := by
    induction h with
    | rel x y hxy => exact hxy.resolve_right fun ⟨_, c, hc, _⟩ => hG c hc
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  unfold blockOf
  congr 1
  ext f
  exact ⟨fun h => (key h).symm, fun h => h ▸ .refl e⟩

/-!
21. Show that for `n ≥ 1` a graph is `n`-colourable iff each of its blocks is. Hint:
the forward direction follows from `blockOf_le`. For the reverse direction use the De
Bruijn–Erdős theorem (`colorable_of_forall_finite_subgraph_colorable`) to reduce to a
finite subgraph `H`, which is colourable by `colorable_of_forall_block` provided its
blocks are. Each block of `H` maps into a block of `G` via `blockOfHom` applied to
`H.hom`.

A colouring of `G` restricts to each block, since blocks are subgraphs of `G`. For
the converse, by De Bruijn–Erdős it suffices to colour every finite subgraph `H` of
`G`. Each block of `H` maps, via the injective homomorphism `H.hom`, into a block of
`G` (`blockOfHom`), so a colouring of the blocks of `G` restricts to a colouring of
the blocks of `H`, and `colorable_of_forall_block` colours `H`.
-/
theorem colorable_iff_forall_block {n : ℕ} (hn : 1 ≤ n) :
    G.Colorable n ↔ ∀ B : G.Block, B.toGraph.Colorable n := by
  constructor
  · -- a colouring of `G` restricts to every block, since each block is a subgraph.
    intro hG B
    induction B using Quotient.inductionOn' with
    | h e => exact hG.mono_left (G.blockOf_le e.2)
  · intro hcol
    classical
    -- by De Bruijn–Erdős it suffices to colour every finite subgraph `H` of `G`
    refine colorable_of_forall_finite_subgraph_colorable fun H hf => ?_
    have := hf.to_subtype
    refine colorable_of_forall_block hn H.coe fun B => ?_
    induction B using Quotient.inductionOn' with
    | h e =>
      -- the block of `e` in `H` maps into the block of `e.map H.hom` in `G`
      obtain ⟨C⟩ := hcol
        (G.blockMk ⟨(e : Sym2 H.verts).map H.hom, H.hom.map_mem_edgeSet e.2⟩)
      exact ⟨C.comp (blockOfHom H.hom Subgraph.hom_injective e)⟩

/-! END SOLUTIONS -/



end SimpleGraph
