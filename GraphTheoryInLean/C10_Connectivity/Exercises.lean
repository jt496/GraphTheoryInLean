/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
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
def botComponentEquiv' : (⊥ : SimpleGraph V).ConnectedComponent ≃ V :=
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
from `isAcyclic_pathNat` using `IsAcyclic.comap`.
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
the degree of any of its vertices.

Hint: every vertex `u ≠ v` has degree at least one
(`Preconnected.degree_pos_of_nontrivial`), so
`degree u + (if G.degree u = 1 then 1 else 0)` is at least 2. Sum this over all
vertices and compare with `IsTree.card_edgeFinset` and the handshake lemma in the
form `sum_degrees_eq_twice_card_edges'` from [The Handshake
Lemma](#section-the-handshake-lemma).
-/
open Finset in
lemma IsTree.degree_le_card_leaves' [Fintype V] [G.LocallyFinite] (h : G.IsTree)
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
Hint: search Mathlib (see [Finding Lemmas](#section-finding-lemmas)) for a lemma
about `induce` and a vertex of degree one.
-/
example [G.LocallyFinite] (hT : G.IsTree) {v : V}
    (hv : G.degree v = 1) : (G.induce {v}ᶜ).IsTree := by
  sorry

/-!
12. Use Euler's theorem (`Connected.exists_isEulerian_circuit`) to show that the
complete graph `K[2 * n + 3]` has an Eulerian circuit, and so does the hypercube
`Q[2 * n + 2]`.
-/
example (n : ℕ) : ∃ u, ∃ p : K[2 * n + 3].Walk u u, p.IsEulerian := by
  sorry

example (n : ℕ) : ∃ u, ∃ p : Q[2 * n + 2].Walk u u, p.IsEulerian := by
  sorry

/-!
13. Show that a `k`-vertex-connected graph has minimum degree at least `k`. Hint:
`exists_minimal_degree_vertex` and `IsVertexConnected.le_degree`.
-/
lemma IsVertexConnected.le_minDegree' {k : ℕ∞} [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] (hG : G.IsVertexConnected k) : k ≤ G.minDegree := by
  sorry

/-!
14. Exercises 14–16 show that if `G` is connected and `k`-vertex-connected then
`G □ K₂` is `(k + 1)`-vertex-connected, and deduce that the hypercube `Q[n]` is
`n`-vertex-connected.

For a finset `S` of vertices of `G □ K₂` and `b : Bool`, let `S.fiberProj b` be the
finset of vertices `z` of `G` whose copy `(z, b)` in the `G`-fibre at `b` lies in
`S`.
-/
/-- The vertices `z` of `G` whose copy `(z, b)` in the `G`-fibre at `b` of `G □ K₂`
lies in `S`. -/
noncomputable def _root_.Finset.fiberProj (S : Finset (V × Bool)) (b : Bool) :
    Finset V :=
  S.preimage (·, b) (Prod.mk_left_injective b).injOn

@[simp] lemma _root_.Finset.mem_fiberProj {S : Finset (V × Bool)} {b : Bool}
    {z : V} :
    z ∈ S.fiberProj b ↔ (z, b) ∈ S := Finset.mem_preimage

/-!
Show that if `0 < k` and `S` has at most `k` elements then some `G`-fibre contains
less than `k` vertices of `S`.

Hint: the sizes of `S.fiberProj false` and `S.fiberProj true` add up to the size of
`S`; use `Finset.card_preimage` and `Finset.card_filter_add_card_filter_not`.
-/
lemma _root_.Finset.exists_fiberProj_card_lt' {k : ℕ} {S : Finset (V × Bool)}
    (hS : S.card ≤ k) (hk : 0 < k) : ∃ b, (S.fiberProj b).card < k := by
  sorry

/-!
15. Let `G` be `k`-vertex-connected and let `S` be a finset of at most `k` vertices
of `G □ K₂`. Show that from any vertex `(z, c)` not in `S` there is a walk into the
`G`-fibre at `b` that avoids `S`.

Hint: if `c ≠ b` and `(z, b) ∈ S`, find a neighbour `w` of `z` such that neither
`(w, false)` nor `(w, true)` lies in `S`: `z` has at least `k` neighbours by
`IsVertexConnected.le_encard_neighborSet`, but less than `k` elements of `S` have a
first coordinate other than `z`. Then step to `(w, c)` and cross to `(w, b)`.
-/
lemma IsVertexConnected.exists_walk_to_fiber' {k : ℕ} (hG : G.IsVertexConnected k)
    {S : Finset (V × Bool)} (hS : S.card ≤ k) {z : V} {c : Bool} (hzc : (z, c) ∉ S)
    (b : Bool) :
    ∃ (z' : V) (p : (G □ (⊤ : SimpleGraph Bool)).Walk (z, c) (z', b)),
      ∀ x ∈ p.support, x ∉ S := by
  sorry

/-!
16. Mathlib's `Walk.boxProdLeft` copies a walk of `G` into the `G`-fibre at `b` of
`G □ H`. It is defined as a `Walk.map`, but its type records the endpoints as
`(u, b)` and `(v, b)`, whereas the endpoints of the `Walk.map` walk only reduce to
these after unfolding `boxProdLeft`. We record the support of the copy as a `simp`
lemma.
-/
@[simp] lemma Walk.support_boxProdLeft {β : Type*} (H : SimpleGraph β) (b : β)
    {u v : V} (p : G.Walk u v) :
    (p.boxProdLeft H b).support = p.support.map (·, b) :=
  Walk.support_map _ _

/-!
Show that if `G` is connected and `k`-vertex-connected then `G □ K₂` is
`(k + 1)`-vertex-connected, and deduce that the hypercube `Q[n]` is
`n`-vertex-connected. (For `k ≥ 1` connectedness follows from
`k`-vertex-connectivity, but two isolated vertices form a `0`-vertex-connected graph
`G` for which `G □ K₂` is disconnected.)

Hint: `G □ K₂` has twice as many vertices as `G`, and by
`IsVertexConnected.of_finset` it is enough to avoid finsets `S`. If `k = 0` then `S`
is empty and `G □ K₂` is connected by `Connected.boxProd`. Otherwise, given vertices
`(u, c)` and `(v, d)` not in `S`, pick `b` such that the `G`-fibre at `b` contains
less than `k` vertices of `S` (Exercise 14), walk from both vertices into the
`G`-fibre at `b` avoiding `S` (Exercise 15), and join the ends of these walks by a
walk in `G` avoiding `S.fiberProj b`, copied into the `G`-fibre at `b` with
`Walk.boxProdLeft`.
-/
lemma IsVertexConnected.boxProd_top_bool' {k : ℕ} (hG : G.IsVertexConnected k)
    (hG_conn : G.Connected) :
    (G □ (⊤ : SimpleGraph Bool)).IsVertexConnected (k + 1) := by
  sorry

lemma isVertexConnected_hypercube' {n : ℕ} : Q[n].IsVertexConnected n := by
  sorry

/-!
17. Deduce that the hypercube `Q[n]` is `n`-edge-connected, and that `Q[n + 2]` has
no bridges. Hint: Exercise 16 and `IsVertexConnected.isEdgeConnected`. Then
`Q[n + 2]` is `2`-edge-connected by `IsEdgeConnected.anti`; now use
`isBridge_iff_not_isEdgeReachable_two`.
-/
lemma isEdgeConnected_hypercube' {n : ℕ} : Q[n].IsEdgeConnected n := by
  sorry

example (n : ℕ) {u v : HypercubeVert (n + 2)} (h : Q[n + 2].Adj u v) :
    ¬ Q[n + 2].IsBridge s(u, v) := by
  sorry

/-!
18. Show that the edge connectivity of a finite graph with at least two vertices is
at most its minimum degree. Together with `vertexConnectivity_le_edgeConnectivity`
this gives Whitney's inequalities
[Whitney 1932](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-whitney-1932)
`κ(G) ≤ λ(G) ≤ δ(G)`. Hint: `exists_minimal_degree_vertex` and
`edgeConnectivity_le_degree`.
-/
lemma edgeConnectivity_le_minDegree' [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : λ(G) ≤ G.minDegree := by
  sorry

/-!
19. The *bowtie* consists of two triangles `0, 1, 2` and `0, 3, 4` sharing the vertex
`0`. Instance search does not unfold the definition of `bowtie`, so we supply its
`DecidableRel` instance by hand; this lets `decide` check properties of the bowtie.
-/
/-- The *bowtie*: two triangles `0, 1, 2` and `0, 3, 4` sharing the vertex `0`. -/
def bowtie : SimpleGraph (Fin 5) :=
  fromRel fun i j => (i, j) ∈ [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]

instance : DecidableRel bowtie.Adj := inferInstanceAs (DecidableRel (fromRel _).Adj)

/-!
Show that `κ(bowtie) < λ(bowtie)`, so the first of Whitney's inequalities can be
strict. Hint: the bowtie is `2`-edge-connected by
`isEdgeConnected_two_iff_forall_preconnected` and `decide`. It is not
`2`-vertex-connected, by `isVertexConnected_iff_induce` with `S = {0}` and `decide`.
Finally use `le_edgeConnectivity_iff` and `le_vertexConnectivity_iff`.
-/
example : κ(bowtie) < λ(bowtie) := by
  sorry

/-!
20. The *barbell* consists of two copies of `K[4]`, on `0, 1, 2, 3` and on
`4, 5, 6, 7`, joined by the edge `3 — 4`. As for the bowtie, we supply its
`DecidableRel` instance by hand.
-/
/-- The *barbell*: two copies of `K[4]`, on `0, 1, 2, 3` and `4, 5, 6, 7`, joined by
the edge `3 — 4`. -/
def barbell : SimpleGraph (Fin 8) :=
  fromRel fun i j => (i < 4 ∧ j < 4) ∨ (4 ≤ i ∧ 4 ≤ j) ∨ (i = 3 ∧ j = 4)

instance : DecidableRel barbell.Adj := inferInstanceAs (DecidableRel (fromRel _).Adj)

/-!
Show that `λ(barbell) < δ(barbell)`, so the second of Whitney's inequalities can also
be strict. Hint: the barbell is not `2`-edge-connected, by
`isEdgeConnected_two_iff_forall_preconnected` with `e = s(3, 4)` and `decide`. Every
vertex has degree at least `3`, by `le_minDegree_of_forall_le_degree` and `decide`.
-/
example : λ(barbell) < δ(barbell) := by
  sorry

/-!
21. Show that the vertex connectivity of the hypercube `Q[n]` is exactly `n`. Hint:
the lower bound is Exercise 16 (via `le_vertexConnectivity_iff`);
for the upper bound use `vertexConnectivity_le_encard_neighborSet` at any vertex,
together with `IsRegularOfDegree.hypercube`.
-/
lemma vertexConnectivity_hypercube' (n : ℕ) : κ(Q[n]) = n := by
  sorry

/-!
22. Show that the edge connectivity of `Q[n + 1]` is `n + 1`, but that the edge
connectivity of `Q[0]` is `⊤`. Hint: use `vertexConnectivity_le_edgeConnectivity` and
`edgeConnectivity_le_degree`, which needs a `Nontrivial (HypercubeVert (n + 1))`
instance, and `edgeConnectivity_of_subsingleton`. Instance search deliberately does
not see through `HypercubeVert`, so you will have to supply these instances yourself,
for example with `inferInstanceAs (Nontrivial (HypercubeVert n × Bool))`.
-/
lemma edgeConnectivity_hypercube_succ' (n : ℕ) : λ(Q[n + 1]) = n + 1 := by
  sorry

lemma edgeConnectivity_hypercube_zero' : λ(Q[0]) = ⊤ := by
  sorry

/-!
23. Show that in a forest the block of an edge `u — v` is `G.subgraphOfAdj h`, the
subgraph consisting of that edge and its two endpoints. Hint: show that
block-equivalent edges of a forest are equal, by induction on `BlockEquivalent`, and
use `blockMk_eq_blockMk_iff`.
-/
lemma IsAcyclic.toSubgraph_blockMk' (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) :
    h.block.toSubgraph = G.subgraphOfAdj h := by
  sorry

/-!
24. Show that for `n ≥ 1` a graph is `n`-colourable iff each of its blocks is. Hint:
the forward direction follows from `Colorable.of_hom` and `Subgraph.hom`. For the
reverse direction use the De Bruijn–Erdős theorem
(`colorable_of_forall_finite_subgraph_colorable`) to reduce to a finite subgraph `H`,
which is colourable by `colorable_of_forall_block` provided its blocks are. Each
block of `H` maps into a block of `G` along the copy `H.coeCopy`
(`Block.map_toSubgraph_le`), and `Subgraph.homOfMapLE` turns this into a
homomorphism.
-/
theorem colorable_iff_forall_block' {n : ℕ} (hn : 1 ≤ n) :
    G.Colorable n ↔ ∀ B : G.Block, B.toSubgraph.coe.Colorable n := by
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
    use .cons h <| .cons (by simp) .nil
  | .inr b =>
    exact (by simp : K[s + 1, t + 1].Adj (.inl 0) (.inr b)).reachable

/-!
3. Construct the equivalence between the connected components of the empty graph and
its vertex type. Hint: `ConnectedComponent.lift` and `ConnectedComponent.ind`; what
does a walk in `⊥` look like?

Any walk in `⊥` is `nil`, so reachability in `⊥` is equality and
`connectedComponentMk` is a bijection.
-/
def botComponentEquiv : (⊥ : SimpleGraph V).ConnectedComponent ≃ V where
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
from `isAcyclic_pathNat` using `IsAcyclic.comap`.

The path graph is connected, and `Fin.val` is an injective homomorphism from
`P[n + 1]` into the infinite path `pathNat`, which is acyclic. So any cycle in
`P[n + 1]` would map to a cycle in `pathNat`.
-/
example (n : ℕ) : P[n + 1].IsTree :=
  ⟨connected_pathGraph_add_one n,
    isAcyclic_pathNat.comap ⟨Fin.val, by grind [pathGraph_adj]⟩ Fin.val_injective⟩

/-!
We can also prove that the path graph is a tree by showing that it has the correct
number of edges (`isTree_iff_connected_and_card`).
-/
example (n : ℕ) : P[n + 1].IsTree := by
  apply isTree_iff_connected_and_card.2 ⟨connected_pathGraph_add_one _,?_⟩
  simp only [Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin,
            Nat.add_right_cancel_iff]
  -- show `P[n + 1].edgeFinset.card = n` by exhibiting a bijection from `Fin n`
  have he : P[n + 1].edgeFinset = Finset.univ.image
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
the degree of any of its vertices.

Hint: every vertex `u ≠ v` has degree at least one
(`Preconnected.degree_pos_of_nontrivial`), so
`degree u + (if G.degree u = 1 then 1 else 0)` is at least 2. Sum this over all
vertices and compare with `IsTree.card_edgeFinset` and the handshake lemma in the
form `sum_degrees_eq_twice_card_edges'` from [The Handshake
Lemma](#section-the-handshake-lemma).
-/
open Finset in
lemma IsTree.degree_le_card_leaves [Fintype V] [G.LocallyFinite] (h : G.IsTree)
    (v : V) : G.degree v ≤ #{u | G.degree u = 1} := by
  classical
  -- each vertex `u ≠ v` has degree ≥ 1, so its degree plus leaf indicator is ≥ 2
  have hge : ∀ u ∈ univ.erase v,
      2 ≤ G.degree u + if G.degree u = 1 then 1 else 0 := by
    intro u hu
    have : Nontrivial V := ⟨u, v, ne_of_mem_erase hu⟩
    have := h.connected.preconnected.degree_pos_of_nontrivial u
    split_ifs <;> grind
  have hsum := sum_le_sum hge
  rw [sum_const, card_erase_of_mem (mem_univ v), card_univ, smul_eq_mul] at hsum
  -- split off `v` from the full sum, which is `2 * #edges + #leaves`
  have hsplit := add_sum_erase univ
    (fun u => G.degree u + if G.degree u = 1 then 1 else 0) (mem_univ v)
  have htot : ∑ u, (G.degree u + if G.degree u = 1 then 1 else 0)
      = 2 * #G.edgeFinset + #{u | G.degree u = 1} := by
    rw [sum_add_distrib, G.sum_degrees_eq_twice_card_edges', card_filter]
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
Hint: search Mathlib (see [Finding Lemmas](#section-finding-lemmas)) for a lemma
about `induce` and a vertex of degree one.
-/
example [G.LocallyFinite] (hT : G.IsTree) {v : V}
    (hv : G.degree v = 1) : (G.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv, hT.isAcyclic.induce _⟩

/-!
12. Use Euler's theorem (`Connected.exists_isEulerian_circuit`) to show that the
complete graph `K[2 * n + 3]` has an Eulerian circuit, and so does the hypercube
`Q[2 * n + 2]`.

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
  (connected_hypercube _).exists_isEulerian_circuit fun v => by
    rw [IsRegularOfDegree.hypercube]
    exact ⟨n + 1, by grind⟩

/-!
13. Show that a `k`-vertex-connected graph has minimum degree at least `k`. Hint:
`exists_minimal_degree_vertex` and `IsVertexConnected.le_degree`.
-/
lemma IsVertexConnected.le_minDegree {k : ℕ∞} [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] (hG : G.IsVertexConnected k) : k ≤ G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact hG.le_degree v

/-!
14. Show that if `0 < k` and `S` has at most `k` elements then some `G`-fibre
contains less than `k` vertices of `S`.

Hint: the sizes of `S.fiberProj false` and `S.fiberProj true` add up to the size of
`S`; use `Finset.card_preimage` and `Finset.card_filter_add_card_filter_not`.

The two sizes add up to at most `k`, so they cannot both be at least `k > 0`.
-/
lemma _root_.Finset.exists_fiberProj_card_lt {k : ℕ} {S : Finset (V × Bool)}
    (hS : S.card ≤ k) (hk : 0 < k) : ∃ b, (S.fiberProj b).card < k := by
  classical
  have hc (b : Bool) : (S.fiberProj b).card = (S.filter (·.2 = b)).card := by
    rw [Finset.fiberProj, Finset.card_preimage]; congr 1; ext ⟨x, c⟩; simp [eq_comm]
  have h := Finset.card_filter_add_card_filter_not (s := S) (fun x => x.2 = false)
  simp only [Bool.not_eq_false, ← hc] at h
  grind

/-!
15. Let `G` be `k`-vertex-connected and let `S` be a finset of at most `k` vertices
of `G □ K₂`. Show that from any vertex `(z, c)` not in `S` there is a walk into the
`G`-fibre at `b` that avoids `S`.

Hint: if `c ≠ b` and `(z, b) ∈ S`, find a neighbour `w` of `z` such that neither
`(w, false)` nor `(w, true)` lies in `S`: `z` has at least `k` neighbours by
`IsVertexConnected.le_encard_neighborSet`, but less than `k` elements of `S` have a
first coordinate other than `z`. Then step to `(w, c)` and cross to `(w, b)`.

If `c = b` the empty walk works, and if `(z, b) ∉ S` we cross directly. Otherwise
the counting argument of the hint gives a neighbour `w` of `z` with both copies
outside `S`, and we step to `(w, c)` and cross to `(w, b)`.
-/
private lemma exists_good_neighbor {k : ℕ} (hG : G.IsVertexConnected k)
    {S : Finset (V × Bool)} (hS : S.card ≤ k) {z : V} {b : Bool} (hzb : (z, b) ∈ S) :
    ∃ w, G.Adj z w ∧ ∀ c, (w, c) ∉ S := by
  classical
  by_contra! h
  have hz : z ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hzb
  -- every neighbour of `z` is a first coordinate of `S` other than `z`
  have hsub : G.neighborSet z ⊆ ↑((S.image Prod.fst).erase z) := fun w hw => by
    obtain ⟨c, hc⟩ := h w hw
    exact Finset.mem_erase.mpr ⟨hw.ne', Finset.mem_image_of_mem Prod.fst hc⟩
  have hk := (hG.le_encard_neighborSet z).trans (Set.encard_le_encard hsub)
  grind [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le, Finset.card_erase_of_mem hz]

lemma IsVertexConnected.exists_walk_to_fiber {k : ℕ} (hG : G.IsVertexConnected k)
    {S : Finset (V × Bool)} (hS : S.card ≤ k) {z : V} {c : Bool} (hzc : (z, c) ∉ S)
    (b : Bool) :
    ∃ (z' : V) (p : (G □ (⊤ : SimpleGraph Bool)).Walk (z, c) (z', b)),
      ∀ x ∈ p.support, x ∉ S := by
  by_cases hcb : c = b
  · subst hcb
    exact ⟨z, .nil, by simp [hzc]⟩
  have hcross (w : V) : (G □ ⊤).Adj (w, c) (w, b) := boxProd_adj_right.mpr hcb
  by_cases hzb : (z, b) ∈ S
  · obtain ⟨w, hzw, hw⟩ := exists_good_neighbor hG hS hzb
    exact ⟨w, .cons (boxProd_adj_left.mpr hzw) (hcross w).toWalk, by simp [hzc, hw]⟩
  · exact ⟨z, (hcross z).toWalk, by simp [hzc, hzb]⟩

/-!
16. Show that if `G` is connected and `k`-vertex-connected then `G □ K₂` is
`(k + 1)`-vertex-connected, and deduce that the hypercube `Q[n]` is
`n`-vertex-connected. (For `k ≥ 1` connectedness follows from
`k`-vertex-connectivity, but two isolated vertices form a `0`-vertex-connected graph
`G` for which `G □ K₂` is disconnected.)

Hint: `G □ K₂` has twice as many vertices as `G`, and by
`IsVertexConnected.of_finset` it is enough to avoid finsets `S`. If `k = 0` then `S`
is empty and `G □ K₂` is connected by `Connected.boxProd`. Otherwise, given vertices
`(u, c)` and `(v, d)` not in `S`, pick `b` such that the `G`-fibre at `b` contains
less than `k` vertices of `S` (Exercise 14), walk from both vertices into the
`G`-fibre at `b` avoiding `S` (Exercise 15), and join the ends of these walks by a
walk in `G` avoiding `S.fiberProj b`, copied into the `G`-fibre at `b` with
`Walk.boxProdLeft`.

The walk from `(u, c)` into the `G`-fibre at `b`, the copy of the walk in `G`, and
the reverse of the walk from `(v, d)` into the `G`-fibre at `b` together form a walk
from `(u, c)` to `(v, d)`. It avoids `S`, since the copy only visits vertices
`(z, b)` with `z ∉ S.fiberProj b`. Since `Q[n + 1]` is `Q[n] □ K₂`, the statement
about the hypercube follows by induction on `n`.
-/
lemma IsVertexConnected.boxProd_top_bool {k : ℕ} (hG : G.IsVertexConnected k)
    (hG_conn : G.Connected) :
    (G □ (⊤ : SimpleGraph Bool)).IsVertexConnected (k + 1) := by
  refine .of_finset ?_ ?_
  · -- `|V × Bool| = 2 |V|` and `k + 1 ≤ |V|`
    have h := hG.1
    rw [ENat.card_prod, ENat.card_eq_coe_fintype_card (α := Bool), Fintype.card_bool,
      Nat.cast_ofNat]
    calc (k : ℕ∞) + 1 + 1 ≤ ((k : ℕ∞) + 1) * 2 := by norm_cast; grind
      _ ≤ _ := by gcongr
  intro S hS ⟨u, c⟩ ⟨v, d⟩ hu hv
  replace hS : S.card < k + 1 := by exact_mod_cast hS
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- for `k = 0` the set `S` is empty and `G □ K₂` is connected
    obtain ⟨p⟩ := (hG_conn.boxProd connected_top).preconnected (u, c) (v, d)
    exact ⟨p, by simp [Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hS)]⟩
  have hS' : S.card ≤ k := Nat.le_of_lt_succ hS
  obtain ⟨b, hb⟩ := S.exists_fiberProj_card_lt hS' hk
  obtain ⟨u', pu, hpu⟩ := hG.exists_walk_to_fiber hS' hu b
  obtain ⟨v', pv, hpv⟩ := hG.exists_walk_to_fiber hS' hv b
  obtain ⟨q, hq⟩ := hG.exists_walk (S.fiberProj b) (Nat.cast_lt.mpr hb) u' v'
    (by simpa using hpu _ pu.end_mem_support)
    (by simpa using hpv _ pv.end_mem_support)
  refine ⟨pu.append ((q.boxProdLeft ⊤ b).append pv.reverse), fun x hx => ?_⟩
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse,
    Walk.support_boxProdLeft, List.mem_map] at hx
  grind [Finset.mem_fiberProj]

lemma isVertexConnected_hypercube {n : ℕ} : Q[n].IsVertexConnected n := by
  induction n with
  | zero =>
    refine ⟨?_, fun S hS => absurd hS (by simp)⟩
    simp
  | succ n ih =>
    exact ih.boxProd_top_bool (connected_hypercube n)

/-!
17. Deduce that the hypercube `Q[n]` is `n`-edge-connected, and that `Q[n + 2]` has
no bridges. Hint: Exercise 16 and `IsVertexConnected.isEdgeConnected`. Then
`Q[n + 2]` is `2`-edge-connected by `IsEdgeConnected.anti`; now use
`isBridge_iff_not_isEdgeReachable_two`.
-/
lemma isEdgeConnected_hypercube {n : ℕ} : Q[n].IsEdgeConnected n :=
  isVertexConnected_hypercube.isEdgeConnected

example (n : ℕ) {u v : HypercubeVert (n + 2)} (h : Q[n + 2].Adj u v) :
    ¬ Q[n + 2].IsBridge s(u, v) := fun hb =>
  (isBridge_iff_not_isEdgeReachable_two h).mp hb
    ((isEdgeConnected_hypercube (n := n + 2)).anti (by simp) u v)

/-!
18. Show that the edge connectivity of a finite graph with at least two vertices is
at most its minimum degree. Together with `vertexConnectivity_le_edgeConnectivity`
this gives Whitney's inequalities
[Whitney 1932](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-whitney-1932)
`κ(G) ≤ λ(G) ≤ δ(G)`. Hint: `exists_minimal_degree_vertex` and
`edgeConnectivity_le_degree`.
-/
lemma edgeConnectivity_le_minDegree [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : λ(G) ≤ G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact edgeConnectivity_le_degree v

/-!
19. Show that `κ(bowtie) < λ(bowtie)`, so the first of Whitney's inequalities can be
strict. Hint: the bowtie is `2`-edge-connected by
`isEdgeConnected_two_iff_forall_preconnected` and `decide`. It is not
`2`-vertex-connected, by `isVertexConnected_iff_induce` with `S = {0}` and `decide`.
Finally use `le_edgeConnectivity_iff` and `le_vertexConnectivity_iff`.

In fact `κ(bowtie) = 1` and `λ(bowtie) = 2`, the minimum degree.
-/
example : κ(bowtie) < λ(bowtie) := by
  -- deleting any single edge leaves the bowtie preconnected
  have h2e : bowtie.IsEdgeConnected 2 :=
    isEdgeConnected_two_iff_forall_preconnected.mpr (by decide)
  -- deleting the shared vertex `0` disconnects it
  have h2v : ¬ bowtie.IsVertexConnected 2 := fun h =>
    absurd ((isVertexConnected_iff_induce.mp h).2 {0} (by simp)) (by decide)
  have hκ : κ(bowtie) < 2 := not_le.mp (mt le_vertexConnectivity_iff.mp h2v)
  exact hκ.trans_le (le_edgeConnectivity_iff.mpr h2e)

/-!
20. Show that `λ(barbell) < δ(barbell)`, so the second of Whitney's inequalities can
also be strict. Hint: the barbell is not `2`-edge-connected, by
`isEdgeConnected_two_iff_forall_preconnected` with `e = s(3, 4)` and `decide`. Every
vertex has degree at least `3`, by `le_minDegree_of_forall_le_degree` and `decide`.

In fact `λ(barbell) = 1`, since `3 — 4` is a bridge, and `δ(barbell) = 3`.
-/
example : λ(barbell) < δ(barbell) := by
  -- deleting the bridge `3 — 4` disconnects the barbell
  have h2e : ¬ barbell.IsEdgeConnected 2 := fun h =>
    absurd (isEdgeConnected_two_iff_forall_preconnected.mp h s(3, 4)) (by decide)
  have hl : λ(barbell) < 2 := not_le.mp (mt le_edgeConnectivity_iff.mp h2e)
  -- every vertex has degree at least `3`
  have hδ : 3 ≤ δ(barbell) := barbell.le_minDegree_of_forall_le_degree 3 (by decide)
  exact hl.trans_le (by exact_mod_cast (by norm_num : 2 ≤ 3).trans hδ)

/-!
21. Show that the vertex connectivity of the hypercube `Q[n]` is exactly `n`. Hint:
the lower bound is Exercise 16 (via `le_vertexConnectivity_iff`);
for the upper bound use `vertexConnectivity_le_encard_neighborSet` at any vertex,
together with `IsRegularOfDegree.hypercube`.

The lower bound is `n`-vertex-connectivity of `Q[n]`, and the upper bound is the
degree `n` of any vertex.
-/
lemma vertexConnectivity_hypercube (n : ℕ) : κ(Q[n]) = n := by
  obtain ⟨v⟩ : Nonempty (HypercubeVert n) := inferInstance
  refine le_antisymm ((vertexConnectivity_le_encard_neighborSet v).trans_eq ?_)
    (le_vertexConnectivity_iff.mpr isVertexConnected_hypercube)
  rw [← coe_neighborFinset, Set.encard_coe_eq_coe_finsetCard,
    card_neighborFinset_eq_degree, IsRegularOfDegree.hypercube n v]

/-!
22. Show that the edge connectivity of `Q[n + 1]` is `n + 1`, but that the edge
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
lemma edgeConnectivity_hypercube_succ (n : ℕ) : λ(Q[n + 1]) = n + 1 := by
  have : Nontrivial (HypercubeVert (n + 1)) :=
    inferInstanceAs (Nontrivial (HypercubeVert n × Bool))
  obtain ⟨v⟩ : Nonempty (HypercubeVert (n + 1)) := inferInstance
  refine le_antisymm ((edgeConnectivity_le_degree v).trans_eq ?_) ?_
  · rw [IsRegularOfDegree.hypercube (n + 1) v]; rfl
  · exact_mod_cast (vertexConnectivity_hypercube (n + 1)).symm.le.trans
      vertexConnectivity_le_edgeConnectivity

lemma edgeConnectivity_hypercube_zero : λ(Q[0]) = ⊤ :=
  have : Subsingleton (HypercubeVert 0) := inferInstanceAs (Subsingleton Unit)
  edgeConnectivity_of_subsingleton

/-!
23. Show that in a forest the block of an edge `u — v` is `G.subgraphOfAdj h`, the
subgraph consisting of that edge and its two endpoints. Hint: show that
block-equivalent edges of a forest are equal, by induction on `BlockEquivalent`, and
use `blockMk_eq_blockMk_iff`.

Two distinct edges of a forest never lie on a common cycle, so cycle-equivalence, and
hence block-equivalence, is just equality.
-/
lemma IsAcyclic.toSubgraph_blockMk (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) :
    h.block.toSubgraph = G.subgraphOfAdj h := by
  -- block-equivalent edges of a forest are equal
  have key {f g : Sym2 V} (h : G.BlockEquivalent f g) : f = g := by
    induction h with
    | rel x y hxy => exact hxy.resolve_right fun ⟨_, c, hc, _⟩ => hG c hc
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  ext x y
  · simp only [Block.mem_toSubgraph_verts, subgraphOfAdj_verts, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · -- the edge through `x` is `s(u, v)` itself
      rintro ⟨e, hx, he⟩
      rw [key (blockMk_eq_blockMk_iff.mp he)] at hx
      simpa using hx
    · rintro (rfl | rfl)
      exacts [⟨⟨_, h⟩, Sym2.mem_mk_left _ _, rfl⟩,
        ⟨⟨_, h⟩, Sym2.mem_mk_right _ _, rfl⟩]
  · simp only [blockMk_toSubgraph_adj, subgraphOfAdj_adj]
    refine ⟨fun ⟨_, hy⟩ => key hy, fun hy => ⟨?_, hy ▸ .refl _⟩⟩
    rcases Sym2.eq_iff.mp hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h, h.symm]

/-!
24. Show that for `n ≥ 1` a graph is `n`-colourable iff each of its blocks is. Hint:
the forward direction follows from `Colorable.of_hom` and `Subgraph.hom`. For the
reverse direction use the De Bruijn–Erdős theorem
(`colorable_of_forall_finite_subgraph_colorable`) to reduce to a finite subgraph `H`,
which is colourable by `colorable_of_forall_block` provided its blocks are. Each
block of `H` maps into a block of `G` along the copy `H.coeCopy`
(`Block.map_toSubgraph_le`), and `Subgraph.homOfMapLE` turns this into a
homomorphism.

A colouring of `G` restricts to each block, since blocks are subgraphs of `G`. For
the converse, by De Bruijn–Erdős it suffices to colour every finite subgraph `H` of
`G`. Each block of `H` maps, via the copy `H.coeCopy`, into a block of
`G` (`Block.map_toSubgraph_le`), so a colouring of the blocks of `G` pulls back to a
colouring of the blocks of `H` (`Subgraph.homOfMapLE`), and
`colorable_of_forall_block` colours `H`.
-/
theorem colorable_iff_forall_block {n : ℕ} (hn : 1 ≤ n) :
    G.Colorable n ↔ ∀ B : G.Block, B.toSubgraph.coe.Colorable n := by
  constructor
  · -- a colouring of `G` restricts to every block, along its inclusion into `G`
    exact fun hG B => hG.of_hom B.toSubgraph.hom
  · intro hcol
    -- by De Bruijn–Erdős it suffices to colour every finite subgraph `H` of `G`
    refine colorable_of_forall_finite_subgraph_colorable fun H hf => ?_
    have := hf.to_subtype
    -- each block `B` of `H` maps into the block `B.map H.coeCopy` of `G`
    exact colorable_of_forall_block hn H.coe fun B =>
      (hcol _).of_hom (Subgraph.homOfMapLE _
        (B.map_toSubgraph_le H.coeCopy))

/-! END SOLUTIONS -/



end SimpleGraph
