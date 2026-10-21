import GraphTheoryInLean.C06_Cliques.Exercises
import GraphTheoryInLean.C07_Colorings.C07_Colorings
import GraphTheoryInLean.C08_Walks.Exercises
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
namespace SimpleGraph
open Subgraph
section basics
variable {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
/-!
Informally, a *subgraph* of a graph `G` is a graph `H` with `V(H) ⊆ V(G)` and
`E(H) ⊆ E(G)`. We have already seen the subgraph order `H ≤ G` on `SimpleGraph V`,
which describes subgraphs with *the same vertex set* (or more precisely the same
vertex type). For a general subgraph we need to allow the vertex set to vary. Mathlib
formalizes this with the type `SimpleGraph.Subgraph`.

In this chapter we introduce `SimpleGraph.Subgraph` and the bounded lattice structure
of subgraphs. We then look at ways of constructing subgraphs: from vertices, edges
and walks, by taking induced subgraphs, and by deleting vertices and edges. Since a
`Subgraph` is not a `SimpleGraph` we next consider the ways to convert between the
two (`Subgraph.coe`, `Subgraph.spanningCoe` and `toSubgraph`), spanning subgraphs,
and the parts of the `SimpleGraph` API that have to be duplicated for `Subgraph`.
Since we now have four different ways of talking about subgraphs, we compare them and
discuss when to use each. As a first application we use the *De Bruijn–Erdős theorem*
to extend our greedy colouring bound to infinite graphs. We then introduce maps and
comaps of subgraphs, with subgraphs of the Mycielskian as a worked example.

Matchings are subgraphs, so we next define the *matching number* `ν G` of a graph,
compare it with the *vertex cover number* `τ G` (weak duality `ν G ≤ τ G`), and
compute it for the hypercube and the Mycielskian.

The final section is more advanced: we introduce *partial colourings*, colourings
that need only be valid on a given set of vertices. These are the main tool in our
proof of *Brooks' theorem* in
[Brooks' Theorem*](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-brooks-theorem).

# Subgraphs

Given `G : SimpleGraph V`, `G.Subgraph` is the type of general subgraphs of `G`.
-/
#source Subgraph

/-!
If `H : G.Subgraph` then we have the following data:
-/
#check H.verts      -- `Set V` the vertex set of the subgraph `H`
#check H.Adj        -- `V → V → Prop` the adjacency relation of the subgraph `H`
#check H.adj_sub    -- `H.Adj v w → G.Adj v w` (i.e. `E(H) ⊆ E(G)`)
#check H.edge_vert  -- `H.Adj v w → v ∈ H.verts` edges of `H` only join verts of `H`
#check H.symm       -- `Std.Symm H.Adj`: `H.Adj v w → H.Adj w v` (unoriented edges)

example (H : G.Subgraph) (v w : V) (h : H.Adj v w) : H.Adj w v := h.symm

/-!
In order to prove that two subgraphs `H₁` and `H₂` of `G : SimpleGraph V` are equal
we need to show that they have the same vertex set and the same edges. We can do this
using `ext` as we did for `SimpleGraph V` (`Subgraph` also has the `@[ext]` attribute
on its definition) but now this will give us two goals: one for equality of vertex
sets and one for equality of adjacency relations (edges).
-/

example (H₁ H₂ : G.Subgraph) (h₁ : H₁.verts = H₂.verts)
    (h₂ : ∀ v w, H₁.Adj v w ↔ H₂.Adj v w) : H₁ = H₂ := by
  ext v w
  · rw [h₁]
  · apply h₂

/-!
## The Subgraph Lattice

The subgraphs of a graph `G` form a bounded lattice under the partial order `H₁ ≤ H₂`
defined by `H₁.verts ⊆ H₂.verts` and `H₁.Adj v w → H₂.Adj v w`. (So `H₁ ≤ H₂` means
that all vertices and edges of `H₁` are also vertices and edges of `H₂`.)
-/
example (H₁ H₂ : G.Subgraph) (h : H₁ ≤ H₂) (v w : V) (hadj : H₁.Adj v w) :
    H₂.Adj v w := h.2 hadj

example (H₁ H₂ : G.Subgraph) (h : H₁ ≤ H₂) (v : V) (hv : v ∈ H₁.verts) :
    v ∈ H₂.verts := h.1 hv
/-!
The `inf` of two subgraphs has vertex set given by the intersection of the vertex
sets and edge set given by the intersection of the edge sets. While for `sup` it is
the union of both.
-/
#check Subgraph.verts_inf
#check Subgraph.inf_adj
#check Subgraph.verts_sup
#check Subgraph.sup_adj

/-!
[Figure: Left: a graph $G$. Top: subgraphs $H_1$ (blue) and $H_2$ (red) of $G$, with the vertices they omit dashed. Bottom: their inf $H_1 \sqcap H_2$ and sup $H_1 \sqcup H_2$, with the edges in both subgraphs in green](https://jt496.github.io/GraphTheoryInLean/figures/inf_subgraph.svg)

If `G : SimpleGraph V` then the top subgraph `⊤` of `G` has the same vertex set and
edge set as `G`, so mathematically `⊤ : G.Subgraph` *is* `G` (but with type
`G.Subgraph` rather than `SimpleGraph V`). The bottom subgraph `⊥` has empty vertex
set and edge set.
-/
#check Subgraph.verts_top
#check Subgraph.top_adj
#check Subgraph.verts_bot
#check Subgraph.not_bot_adj

/-!
Recall that `SimpleGraph V` is a Boolean algebra, so any `G : SimpleGraph V` has a
complement `Gᶜ` with `G ⊓ Gᶜ = ⊥` and `G ⊔ Gᶜ = ⊤`.

The `G.Subgraph` lattice is *not* Boolean: in fact it is complemented if and only if
`G` is the empty graph. To see why complements fail to exist, suppose that `G` is not
the empty graph and has an edge `u — v`. Take `H₁` to be the subgraph with vertex set
`{u}` and no edges, and suppose that `H₂` is a complement of `H₁`; i.e. `H₁ ⊓ H₂ = ⊥`
and `H₁ ⊔ H₂ = ⊤`. Since `H₁.verts` and `H₂.verts` are disjoint, neither `H₁` nor
`H₂` can contain the edge, so `H₁ ⊔ H₂` also cannot contain it. (`H : G.Subgraph`
does in fact have a different kind of complement `Hᶜ : G.Subgraph` defined in
Mathlib, but this is the *Heyting complement* of `H`. This is the subgraph of `G`
induced by `H.vertsᶜ`; i.e. `(⊤ : G.Subgraph).induce H.vertsᶜ`. (We leave the proof
as an exercise.))
-/
#synth BooleanAlgebra (SimpleGraph V)
#synth HeytingAlgebra G.Subgraph

/-!
# Constructing Subgraphs

There are several ways to construct a `G.Subgraph`. In this section we look at some
common ones: from a single vertex, edge or walk of `G`; by taking the subgraph
induced on a set of vertices; and by deleting vertices or edges from an existing
subgraph.

## Singletons, Edges and Walks

Any vertex or edge of a `G : SimpleGraph V` gives rise to a subgraph consisting of
that vertex or edge. Similarly any walk gives rise to a subgraph consisting of the
vertices and edges of the walk.
-/
section walksetc
variable {u v w : V}

#source SimpleGraph.singletonSubgraph -- verts := {v}, Adj := ⊥ ...

#source SimpleGraph.subgraphOfAdj -- verts := {v, w}, Adj a b := s(v, w) = s(a, b)

/-!
The `G.Subgraph` corresponding to a walk `p` is the subgraph with vertex set the
vertices of `p` and edge set the edges of `p`.
-/
#source Walk.toSubgraph -- p.toSubgraph : G.Subgraph

/-!
The vertex set of the subgraph of a walk is exactly the set of vertices in its
support.
-/
example (p : G.Walk u v) :
  p.toSubgraph.verts = {w | w ∈ p.support} := p.verts_toSubgraph

/-!
If we append two walks, the subgraph of the resulting walk is the `sup` of the
subgraphs of the original walks.
-/
example (p : G.Walk u v) (q : G.Walk v w) :
  (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph := p.toSubgraph_append _

/-!
We can also talk about the `support` of any subgraph `H : G.Subgraph`, which is the
`Subgraph` analogue of `SimpleGraph.support`; i.e. the set of vertices incident to
edges of the subgraph.
-/
#source Subgraph.support  -- def support (H : Subgraph G) : Set V
                          --        := SetRel.dom {(v, w) | H.Adj v w}

/-!
So we now have three different notions of support: `Walk.support`,
`SimpleGraph.support` and `Subgraph.support`. The last two are mathematically the
same, but `Walk.support` is different in two ways: it is a `List` rather than a
`Set`, and if `p : G.Walk u v` is a `Nil` walk then `p.support = [u]` while
`p.toSubgraph.support = ∅`.
-/
#check Walk.support_nil

example (p : G.Walk u v) (h : p.Nil) : p.toSubgraph.support = ∅ := by
  ext x
  cases h
  simp [Walk.toSubgraph, Subgraph.mem_support]

/-!
For non-nil walks the `Walk.toSubgraph.support` is the same as the set of vertices in
the `List` `Walk.support`.
-/
example (p : G.Walk u v) (h : ¬ p.Nil) [DecidableEq V] :
  p.toSubgraph.support = {w | w ∈ p.support} := by
  ext x
  simp only [Subgraph.mem_support, Walk.adj_toSubgraph_iff_mem_edges,
    Sym2.mem_iff_exists, Walk.mem_support_iff_exists_mem_edges_of_not_nil h]
  grind

/-!
Recall that `Set.ncard` is essentially `Nat.card` for sets: both take the junk value
`0` for infinite types/sets (see
[Cardinality](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-cardinality)).

If `c : G.Walk u u` is a cycle and `v` is a vertex in `c` then the set of neighbours
of `v` in the subgraph corresponding to `c` has cardinality two. (Here
`Subgraph.neighborSet` is the set of neighbours *within* the subgraph; we meet it
properly in
[Duplication](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-duplication).)
-/
example {c : G.Walk u u} (hpc : c.IsCycle) (h : v ∈ c.support) :
  (c.toSubgraph.neighborSet v).ncard = 2 := hpc.ncard_neighborSet_toSubgraph_eq_two h

end walksetc
/-!
## Induced Subgraphs

If `H : G.Subgraph` and `s : Set V` then `H.induce s` is the subgraph of `H` induced
by `s`, and also has type `G.Subgraph`.
-/
#source Subgraph.induce  -- G'.induce s : G.Subgraph (for G' : G.Subgraph)

example {u v : V} (s : Set V) (H : G.Subgraph) :
    (H.induce s).Adj u v ↔ u ∈ s ∧ v ∈ s ∧ H.Adj u v := by rfl

/-!
The vertex set of a subgraph induced by `s : Set V` is `s`. (Notice that this allows
an induced subgraph of a subgraph to have vertices that were not present in the
original subgraph.)
-/
example (s : Set V) {H : G.Subgraph} : (H.induce s).verts = s := rfl

/-!
Recall that Mathlib also has `SimpleGraph.induce`. This gives the induced subgraph of
`G : SimpleGraph V` on a set `s : Set V` as a `SimpleGraph ↑s` (here `↑s` denotes the
subtype of `V` consisting of elements in `s`).

In particular if `G : SimpleGraph V` and `s : Set V` then `(⊤ : G.Subgraph).induce s`
and `G.induce s` both correspond to what we would usually call the subgraph of `G`
induced by `s`. Often `(⊤ : G.Subgraph).induce s` is more convenient to work with
since it has the same vertex type as `G` and adjacency is nicely defined.
-/
example {u v : V} (s : Set V) :
  ((⊤ : G.Subgraph).induce s).Adj u v ↔ u ∈ s ∧ v ∈ s ∧ G.Adj u v := Iff.rfl

/-!
For example expressing adjacency in an induced subgraph of an induced subgraph is
straightforward with `Subgraph.induce`.
-/
example {u v : V} (s t : Set V) : (((⊤ : G.Subgraph).induce s).induce t).Adj u v ↔
    u ∈ s ∩ t ∧ v ∈ s ∩ t ∧ G.Adj u v := Iff.intro (by simp_all) (by simp_all)

/-!
Compare the above with the corresponding statement using `SimpleGraph.induce` below.

Since `G.induce s` is a `SimpleGraph ↑s`, the second `induce` below cannot take a
`Set V`; it needs a `Set ↑s`. To lift `t` to `↑s` we must assume `t ⊆ s` (and even
then the lifted set is written as the preimage `(Subtype.val : s → V) ⁻¹' t`).
Vertices of the graph are doubly nested subtype elements, so the `Adj` arguments have
to be built explicitly out of `u v : V` together with proofs of their memberships.
The resulting statement is almost unreadable (even if the proof is easy).
-/
example {s t : Set V} (hts : t ⊆ s) {u v : V} (hu : u ∈ t) (hv : v ∈ t) :
    ((G.induce s).induce ((Subtype.val : s → V) ⁻¹' t)).Adj
        ⟨⟨u, hts hu⟩, hu⟩ ⟨⟨v, hts hv⟩, hv⟩ ↔ G.Adj u v := Iff.rfl

/-!
As well as constructing induced subgraphs there is a predicate for a subgraph to *be*
induced. A subgraph is induced if whenever we take two vertices from its vertex set
that are adjacent in the original graph then they are also adjacent in the subgraph.
-/
#source Subgraph.IsInduced -- ∀ ⦃v⦄, v ∈ H.verts → ∀ ⦃w⦄, w ∈ H.verts →
                           --   G.Adj v w → H.Adj v w
/-!
So the induced subgraphs are exactly the subgraphs of the form
`(⊤ : G.Subgraph).induce s`.
-/
#check Subgraph.isInduced_iff_exists_eq_induce_top

/-!
## Deleting Vertices and Edges

If `H : G.Subgraph` then we can form a new subgraph by deleting any set of vertices
`s : Set V` from `H` (while also obviously removing any edges incident to those
vertices).

Vertex deletion is defined by taking the subgraph of `H` induced by `H.verts \ s`.
-/
example (s : Set V) {H : G.Subgraph} :
  H.deleteVerts s = H.induce (H.verts \ s) := rfl

/-!
A pair of vertices `v w : V` are adjacent in the subgraph obtained by deleting a
set of vertices `s : Set V` from a subgraph `H : G.Subgraph` if and only if they
are not in `s` and are adjacent in `H`. (Mathlib's `Subgraph.deleteVerts_adj` states
this with the redundant conditions `v ∈ H.verts` and `w ∈ H.verts` included.)
-/
example {v w : V} (s : Set V) {H : G.Subgraph} :
    (H.deleteVerts s).Adj v w ↔ v ∉ s ∧ w ∉ s ∧ H.Adj v w := by
  grind [Subgraph.induce_adj, H.edge_vert, Subgraph.Adj.symm]

/-!
We can also delete a set of edges `s : Set (Sym2 V)` from a subgraph (while leaving
the vertex set unchanged).
-/
#source Subgraph.deleteEdges -- G'.deleteEdges s : G.Subgraph

example {v w : V} (s : Set (Sym2 V)) {H : G.Subgraph} :
    (H.deleteEdges s).Adj v w ↔ H.Adj v w ∧ s(v, w) ∉ s := by rfl

#check Subgraph.deleteEdges_verts -- (G'.deleteEdges s).verts = G'.verts

/-!
[Figure: Left: a graph $G$. Centre: deleting the vertices $v_1$ and $v_3$, which also removes their edges. Right: deleting the edges $v_1 v_4$ and $v_2 v_5$. Removed vertices and edges are dashed](https://jt496.github.io/GraphTheoryInLean/figures/deletion.svg)
-/
/-!
# Subgraphs as Simple Graphs

A `G.Subgraph` is not a `SimpleGraph`, so results about the latter do not
automatically apply to the former. In this section we look at how to pass between
the two: the coercions from a subgraph to a simple graph (and back), spanning
subgraphs, for which the two points of view essentially agree, and the parts of the
`SimpleGraph` API that Mathlib duplicates for `Subgraph`.

## Coercions

For example, mathematically `⊤ : G.Subgraph` is just `G`, but comparing the two is a
type mismatch error:
-/
/-- error:
Type mismatch
  ⊤
has type
  G.Subgraph
but is expected to have type
  SimpleGraph V
-/
#guard_msgs in
#check G = (⊤ : G.Subgraph)
/-!
In order to treat a `G.Subgraph` as a `SimpleGraph` we need to use a *coercion*.

There are two different ways to do this. If `H : G.Subgraph` then `H.coe` gives a
graph on the vertex type `H.verts`, the subtype of `V` consisting of the vertices of
`H`, i.e. `{v // v ∈ H.verts}`. The other coercion is `H.spanningCoe` which gives a
graph on the vertex type `V` with the edges of `H` but with all the vertices of `G`.
-/
#source Subgraph.coe -- H.coe : SimpleGraph ↑H.verts

#source Subgraph.spanningCoe -- H.spanningCoe : SimpleGraph V

example : (⊤ : G.Subgraph).spanningCoe = G := rfl
example : (⊥ : G.Subgraph).spanningCoe = ⊥ := rfl
/-!
The second example hides a change of meaning: `⊥ : G.Subgraph` is the *empty*
subgraph, with no vertices, while `⊥ : SimpleGraph V` has every vertex of `V` and no
edges. This is because `spanningCoe` forgets the vertex set and keeps only the edges,
so it is not injective. Two subgraphs have the same `spanningCoe` iff they have the
same edges, whatever their vertices. (For example the spanning coercion of a
single-vertex subgraph `G.singletonSubgraph v` is also `⊥`; see the exercises.)
-/
#check Subgraph.spanningCoe_inj -- H₁.spanningCoe = H₂.spanningCoe ↔ H₁.Adj = H₂.Adj
/-!
The two coercions are related through `SimpleGraph.spanningCoe` from
[SpanningCoe](https://jt496.github.io/GraphTheoryInLean/Maps/#section-spanningcoe):
if we take the graph `H.coe` on `↑H.verts` and then add back the missing vertices of
`V`, we get `H.spanningCoe`.
-/
#check Subgraph.spanningCoe_coe -- H.coe.spanningCoe = H.spanningCoe
/-!
Note that the word *coercion* is used loosely here: `H.coe` and `H.spanningCoe` are
ordinary functions, not coercions in Lean's technical sense. There is no `Coe`
instance behind them, so Lean never inserts them for you: you must write `H.coe` or
`H.spanningCoe` explicitly to get the corresponding `SimpleGraph`. (An example
of a genuine coercion is the one from `ℕ` to `ℝ`: if `n : ℕ` and `x : ℝ` then `x + n`
type-checks because Lean inserts `↑n : ℝ` automatically. We have in fact just seen an
example of such a coercion: the `↑` in `SimpleGraph ↑H.verts`, which turns the set
`H.verts` into a type.)

In the opposite direction, if `G H : SimpleGraph V` and `H ≤ G` then we can convert
`H` to a `G.Subgraph` using `toSubgraph H h` where `h : H ≤ G`.
-/
#source SimpleGraph.toSubgraph

/-!
## Spanning Subgraphs

A subgraph `H : G.Subgraph` is *spanning* if `H.verts = Set.univ`, i.e. it contains
every vertex in `V`.

[Figure: A graph $G$, a spanning subgraph, and a non-spanning subgraph](https://jt496.github.io/GraphTheoryInLean/figures/spanning_vs_non.svg)
-/
example (H : G.Subgraph) : H.IsSpanning ↔ H.verts = Set.univ := isSpanning_iff

/-!
If `G H : SimpleGraph V` and `h : H ≤ G` then `toSubgraph H h` is a spanning subgraph
of `G`.
-/
example (H : SimpleGraph V) (h : H ≤ G) : (toSubgraph H h).IsSpanning :=
  toSubgraph.isSpanning _ _

/-!
If we take the `spanningCoe` of a `toSubgraph` then we get back the original
`SimpleGraph V`.
-/
example (H : SimpleGraph V) (h : H ≤ G) : (toSubgraph H h).spanningCoe = H := rfl

/-!
The subgraph `⊤` is spanning.
-/
example : (⊤ : G.Subgraph).IsSpanning := fun _ => trivial

/-!
The `spanningCoe` of the `G.Subgraph` consisting of a single edge is the
`SimpleGraph V` constructed from the edge set containing this single edge.
-/
example {v w : V} (hadj : G.Adj v w) :
    (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} :=
  Subgraph.spanningCoe_subgraphOfAdj hadj

/-!
If `H : G.Subgraph` then there is a graph embedding of `H.coe` into `H.spanningCoe`.
-/
#check coeEmbeddingSpanningCoe
/-!
If `H : G.Subgraph` is a spanning subgraph then `H.spanningCoe` and `H.coe` are
isomorphic. (They cannot be equal, since the former is a `SimpleGraph V` while the
latter is a `SimpleGraph ↑H.verts` where `H.verts = Set.univ`.)
-/
example (H : G.Subgraph) (h : H.IsSpanning) :
    H.spanningCoe ≃g H.coe := H.spanningCoeEquivCoeOfSpanning h

/-!
## Duplication

For a `G.Subgraph` we don't have access to the many definitions we have already seen
for `SimpleGraph V` such as `neighborSet`, `degree`, `edgeSet`, `incidenceSet`,
`support`, `map`, `comap` (as well as some we will meet later such as `Connected`).
These have to be defined separately for `G.Subgraph` and then related back to the
original graph `G` when needed. This means there is a certain amount of unavoidable
duplication between the theory of `Subgraph` and `SimpleGraph`. We have already met
`Subgraph.support`; some of the others are listed below.
-/
#source Subgraph.neighborSet  -- the neighbour set of a vertex in a subgraph
#source Subgraph.degree       -- the number of neighbours of a vertex in a subgraph
#source Subgraph.edgeSet      -- the set of edges of a subgraph
#source Subgraph.incidenceSet -- the set of edges incident to a vertex in a subgraph

/-!
The degree of a vertex of a subgraph is at most the degree of that vertex in the
original graph.
-/
#check Subgraph.degree_le

/-!
The duplicated definitions are related to each other by bridging lemmas. For example
`Subgraph.coe_degree` says that the degree of `v` in the graph `H.coe` is its degree
in the subgraph `H`. This lets us apply a theorem about degrees in a `SimpleGraph` to
a subgraph, as we do in the proof of `colorable_of_degree_le` below.
-/
#check Subgraph.coe_degree -- H.coe.degree v = H.degree ↑v

/-!
## Which Notion of Subgraph?

We now have four different ways of saying that `H` is a subgraph of `G`. Which one
we choose can make a big difference to how easy a proof is.

| Representation | Vertex type | Use it when |
| :--- | :--- | :--- |
| `H ≤ G` | `V` | every vertex is kept, e.g. deleting edges |
| `G.induce s`, `H.coe` | `↑s`, `↑H.verts` | you need `SimpleGraph` theorems |
| `H : G.Subgraph` | `V` | the vertex set varies, e.g. matchings |
| `Copy A G`, `A ⊑ G` | any type | `A` is a fixed graph, e.g. `A`-free graphs |

* `H ≤ G` with `H : SimpleGraph V`
  ([Order](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-order))
  keeps the vertex type, so the whole `SimpleGraph` API applies and these subgraphs
  form a Boolean algebra. It is the right choice when all vertices are kept, as for
  `G.deleteEdges s`.
* `G.induce s`
  ([Induced Subgraphs via Comap](https://jt496.github.io/GraphTheoryInLean/Maps/#section-induced-subgraphs-via-comap))
  and `H.coe` are genuine `SimpleGraph`s, so every theorem about `SimpleGraph`
  applies to them, but their vertices live in a subtype. We pay for this whenever we
  pass between `v : V` and `⟨v, hv⟩ : ↑s`. The De Bruijn–Erdős theorem below is a
  typical use: Mathlib states it for the graphs `H.coe` of finite subgraphs `H`.
* `H : G.Subgraph` lets the vertex set vary inside `V`, and the subgraphs form a
  lattice. Use it when Mathlib defines the notion you need for subgraphs, such as
  `Walk.toSubgraph` or matchings
  ([Matching Number](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-matching-number)).
  A matching must be a `G.Subgraph`: its vertex set is the set of matched vertices,
  and a *perfect* matching is one that is spanning.
* `Copy A G` is a labelled copy of a graph `A` whose
  vertices may have any type, and `A ⊑ G` says that such a copy exists. Use it to
  talk about containment (or non-containment) of a fixed graph, as in `A.Free G`.

We have already met most of the conversions between these: `toSubgraph H h` turns
`h : H ≤ G` into a `G.Subgraph`, while `H.spanningCoe` and `H.coe` turn
`H : G.Subgraph` into a `SimpleGraph`. Copies and subgraphs are related by the
following three definitions.
-/
#source Copy.toSubgraph -- toSubgraph (f : Copy A B) : B.Subgraph := .map f.toHom ⊤
#source Copy.isoToSubgraph -- (f : Copy A B) : A ≃g f.toSubgraph.coe
#source Subgraph.coeCopy -- (H : G.Subgraph) : Copy H.coe G
/-!
Finally there are useful hybrids. When we define partial colourings in
[Partial Colourings*](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-partial-colourings)
we will use the graph `((⊤ : G.Subgraph).induce s).spanningCoe` whose edges are those
of `G` induced by `s`. Since it is a `SimpleGraph V`, we can use the
`SimpleGraph.Coloring` API.

## De Bruijn–Erdős Theorem

The *De Bruijn–Erdős theorem* says that if every finite subgraph of a (possibly
infinite) graph `G` is `n`-colourable then `G` itself is `n`-colourable.

Mathlib contains the following natural generalization of this theorem: if every
finite subgraph of `G` has a homomorphism to a *finite* graph `F` then there is a
homomorphism from `G` to `F`. (The finiteness of `F` cannot be
dropped: every finite subgraph of `⊤ : SimpleGraph ℕ` has a homomorphism to the
disjoint union of all the complete graphs `K[n]`, but `⊤` itself does not; see the
exercises for details.)
-/
#check nonempty_hom_of_forall_finite_subgraph_hom

/-!
Since an `n`-colouring is a homomorphism to`K[n]`, the De Bruijn–Erdős theorem is the
special case in which `F` is `K[n]`.
-/
/-- *De Bruijn–Erdős*: if every finite subgraph of `G` is `n`-colourable then `G` is
`n`-colourable. -/
theorem colorable_of_forall_finite_subgraph_colorable {n : ℕ}
    (h : ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable n) : G.Colorable n :=
  nonempty_hom_of_forall_finite_subgraph_hom fun H hH => (h H hH).some

/-!
This allows us to give the general greedy colouring bound using our earlier result
for countable graphs, `colorable_of_degree_le_of_countable`, since a finite subgraph
is countable.
-/
theorem colorable_of_degree_le {Δ : ℕ} [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ Δ) : G.Colorable (Δ + 1) :=
  colorable_of_forall_finite_subgraph_colorable fun H hH => by
    classical
    have := hH.to_subtype
    exact colorable_of_degree_le_of_countable fun _ =>
      H.coe_degree _ ▸ (H.degree_le _).trans (hdeg _)

/-!
It remains to explain why `nonempty_hom_of_forall_finite_subgraph_hom` is true.

If `G` is finite there is nothing to prove, since `G` is then a finite subgraph of
itself, so suppose that `G` is infinite. The standard proof is a compactness
argument. Let `W` be the vertex type of `F`, with the discrete topology. Since `W` is
finite, the space of all functions `V → W` is compact by Tychonoff's theorem. A
homomorphism from `G` to `F` is a function `φ : V → W` satisfying one condition for
each edge `u — v` of `G`, namely that `φ u` and `φ v` are adjacent in `F`. Let
`A ⊆ W × W` be the set of pairs `(a, b)` with `a` adjacent to `b` in `F`. For each
edge `u — v` of `G`, let `πᵤᵥ : (V → W) → W × W` be the projection
`πᵤᵥ(φ) = (φ u, φ v)` onto the coordinates `u` and `v`. The functions satisfying the
condition for `u — v` then form the set `πᵤᵥ⁻¹(A)`, which is closed: `πᵤᵥ` is
continuous, being a projection in the product topology, and every subset of the
discrete space `W × W` is closed.

The homomorphisms from `G` to `F` are exactly the functions in the intersection of
all the sets `πᵤᵥ⁻¹(A)`, so we must show that this intersection is nonempty. In a
compact space, a family of closed sets has nonempty intersection provided it has the
*finite intersection property*: any finitely many of the sets have a common point.
Given finitely many edges of `G`, let `H` be the finite subgraph consisting of these
edges and their endpoints. By hypothesis there is a homomorphism from `H` to `F`, and
extending it arbitrarily to the other vertices gives a function in the sets
`πᵤᵥ⁻¹(A)` for all of the given edges.

Mathlib organizes the argument differently, so that most of it becomes an instance of
a general compactness result. Instead of a single function on all of `V`, it looks
for a homomorphism from each finite subgraph, chosen so that they fit together. A
*consistent family* consists of a homomorphism `ψ H` from `H` to `F` for each finite
subgraph `H` of `G`, such that whenever `H₁ ≤ H₂`, the homomorphism `ψ H₁` is the
restriction of `ψ H₂` to `H₁`.

Any homomorphism `φ` from `G` to `F` gives a consistent family, by taking `ψ H` to be
the restriction of `φ` to `H`. Conversely, a consistent family can be glued together
to give a homomorphism from `G` to `F`: send each vertex `v` to its image under
`ψ (G.singletonSubgraph v)`. If `h : G.Adj u v`, then the singleton subgraphs of `u`
and `v` are both contained in the subgraph `G.subgraphOfAdj h` consisting of the edge
`u — v`. So by consistency `u` and `v` have the same images as under
`ψ (G.subgraphOfAdj h)`, and these are adjacent in `F`. Restricting and gluing are
inverse to each other. (In the language of category theory, the consistent families
form the *inverse limit* of the sets of homomorphisms from the finite subgraphs, so
restriction identifies the set of homomorphisms from `G` to `F` with this inverse
limit.)

So it is enough to find a consistent family, and for this only three facts matter:
the finite subgraphs form a *directed* set (any two have a common upper bound, namely
their union); the set of homomorphisms from each finite subgraph to `F` is finite (as
`F` is finite) and nonempty (by hypothesis); and the restriction maps are
*compatible*: restricting a homomorphism from `H` to `H` itself leaves it unchanged,
and if `H₁ ≤ H₂ ≤ H₃`, then restricting a homomorphism from `H₃` to `H₂` and then to
`H₁` gives the same result as restricting it from `H₃` to `H₁` directly.

To find a consistent family we again use Tychonoff's theorem. For each finite
subgraph `H`, let `X H` be the set of homomorphisms from `H` to `F`, with the
discrete topology. Since each `X H` is finite, the product `P` of all the sets `X H`
is compact. A point `ψ` of `P` is a choice of a homomorphism `ψ H` in `X H` for every
finite subgraph `H`. For each pair `H₁ ≤ H₂`, whether `ψ` satisfies the consistency
condition for this pair depends only on `(ψ H₁, ψ H₂)`. So the points satisfying it
form the preimage of a subset of `X H₁ × X H₂` under the projection
`ψ ↦ (ψ H₁, ψ H₂)`, and this set is closed for the same reason as before: the
projection is continuous and `X H₁ × X H₂` is discrete.

The consistent families are exactly the points in the intersection of all these
closed sets, so again it is enough to check the finite intersection property. Given
finitely many pairs `H₁ ≤ H₂`, let `K` be the union of all the subgraphs involved, a
finite subgraph containing each of them; this is where directedness is used. By
hypothesis there is a homomorphism `θ` from `K` to `F`. Take `ψ H` to be the
restriction of `θ` to `H` for each subgraph `H` involved, and choose the other `ψ H`
arbitrarily, which is possible since each `X H` is nonempty. For each of the given
pairs, `ψ H₁` is the restriction of `θ` to `H₁`, which by compatibility is the
restriction to `H₁` of `ψ H₂`. So `ψ` satisfies all of the given conditions, and by
compactness a consistent family exists. The Mathlib proof is this argument, couched
in the language of category theory, with the compactness step proved as a general
result:
-/
open CategoryTheory in
#check nonempty_sections_of_finite_inverse_system

/-!
In our application, `J` is `G.Finsubgraph`, the directed set of finite subgraphs of
`G`. The functor in the theorem packages the sets `X H` and their restriction maps.
It is defined on `Jᵒᵖ` because restriction goes from larger to smaller subgraphs; its
*sections* are the consistent families.
-/

/-!
# Maps and Comaps

`Subgraph.map` is a *pushforward* operation: given a graph homomorphism `f : G →g K`,
between `G : SimpleGraph V` and `K : SimpleGraph W`, and a subgraph `H : G.Subgraph`,
`H.map f` is the subgraph of `K` whose vertex set is `f '' H.verts` and whose edges
are the images `f u — f v` of edges `u — v` of `H`. Note the contrast with
`SimpleGraph.map`
([Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#section-maps)), which takes a
plain function: here `f` must be a homomorphism, since the image has to be a subgraph
of the given graph `K`.
-/
#source Subgraph.map

/-!
There is also `Subgraph.comap` which is a *pullback* operation: given a homomorphism
`f : G →g K` and a subgraph `H` of `K`, `H.comap f` is the subgraph of `G` whose
vertex set is the preimage `f⁻¹' H.verts` and whose edges are those edges `u — v` of
`G` for which `f u` and `f v` are adjacent in `H`.
-/
#source Subgraph.comap

/-!
As for simple graphs
([Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#section-maps)), `map f` and
`comap f` form a Galois connection. Here this holds for every homomorphism `f`, not
just for embeddings: a homomorphism never sends two adjacent vertices to the same
vertex, so no edge is lost when we map forwards.
-/
#check Subgraph.map_le_iff_le_comap -- H.map f ≤ H' ↔ H ≤ H'.comap f

/-!
We have `Subgraph.inclusion` which gives the graph homomorphism between two subgraphs
`H ≤ K` (coerced to `SimpleGraph` on their respective vertex sets).
-/
#check Subgraph.inclusion -- {H K : G.Subgraph} (h : H ≤ K) : H.coe →g K.coe
/-!
We also have `Subgraph.hom` which gives the graph homomorphism from a subgraph `H` to
the original graph `G`.
-/
#check Subgraph.hom -- .. (H : G.Subgraph) : H.coe →g G

/-!
Combining `Subgraph.map` with `Subgraph.hom` gives `Subgraph.coeSubgraph` which
allows us to take a subgraph of a subgraph coerced to `SimpleGraph` and get a
subgraph of the original graph.
-/
#source Subgraph.coeSubgraph --  G'.coe.Subgraph → G.Subgraph

example {A : G.Subgraph} (B : A.coe.Subgraph) (v w : V) : (A.coeSubgraph B).Adj v w
    ↔ ∃ (hv : v ∈ A.verts) (hw : w ∈ A.verts), B.Adj ⟨_, hv⟩ ⟨_, hw⟩ :=
  Subgraph.coeSubgraph_adj B v w

/-!
Combining `Subgraph.comap` with `Subgraph.hom` gives `Subgraph.restrict`: given
subgraphs `A` and `B` of `G`, `A.restrict B` is the part of `B` that lies in `A`, as
a subgraph of `A.coe` (i.e. with vertex type `A.verts`).
-/
#source Subgraph.restrict

/-!
Vertices of `A` are adjacent in `A.restrict B` iff they are adjacent in both `A` and
`B`.
-/
example {A B : G.Subgraph} (v w : A.verts) :
    (A.restrict B).Adj v w ↔ A.Adj v w ∧ B.Adj v w := Iff.rfl

/-!
## Subgraphs of Mycielskians

As worked examples of `Subgraph.map` and `Subgraph.comap` we consider subgraphs of
the Mycielskian `mμ[G]`. If `H : G.Subgraph` then we can map `H` to a subgraph of
`mμ[G]` using the embedding of `G` into `mμ[G]` given by
`Embedding.mycielskianLeft G`.
-/
/--
The subgraph of the Mycielskian `mμ[G]` corresponding to a subgraph `H` of `G`. -/
@[simps!]
def Subgraph.mycielskianSubgraph (H : G.Subgraph) : mμ[G].Subgraph :=
  Subgraph.map (Embedding.mycielskianLeft G).toHom H

/-!
Pulling `mycielskianSubgraph H` back along the same embedding recovers `H`.
-/
lemma Subgraph.comap_mycielskianSubgraph (H : G.Subgraph) :
    H.mycielskianSubgraph.comap (Embedding.mycielskianLeft G).toHom = H := by
  ext v w <;> simp_all [Relation.Map, H.adj_sub]

/-!
Combined with the Galois connection `Subgraph.map_le_iff_le_comap`, this shows that
`mycielskianSubgraph` both preserves and reflects the subgraph order.
-/
lemma Subgraph.mycielskianSubgraph_le_iff {H₁ H₂ : G.Subgraph} :
    H₁.mycielskianSubgraph ≤ H₂.mycielskianSubgraph ↔ H₁ ≤ H₂ := by
  rw [Subgraph.mycielskianSubgraph, Subgraph.map_le_iff_le_comap,
    Subgraph.comap_mycielskianSubgraph]

end basics

/-!
# Matching Number

Mathlib has the predicates `Subgraph.IsMatching` and `Subgraph.IsPerfectMatching`
which say that a `G.Subgraph` is a matching or a perfect matching, as well as
`SimpleGraph.IsMatchingFree` which says that a graph has no perfect matching.
-/
#source Subgraph.IsMatching        -- ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.Adj v w
#source Subgraph.IsPerfectMatching -- M.IsMatching ∧ M.IsSpanning
#source SimpleGraph.IsMatchingFree --  ∀ M : Subgraph G, ¬ M.IsPerfectMatching

/-!
A matching `M` is not spanning in general: its vertex set is the set of *matched*
vertices, and each of these has exactly one neighbour in `M`. A perfect matching is
then simply a spanning matching. (This is why matchings must be `G.Subgraph`s.)

[Figure: Left: a matching $M$, which leaves $c$ and $f$ unmatched. Right: a perfect matching](https://jt496.github.io/GraphTheoryInLean/figures/matching.svg)

Mathlib has the classical existence theorems (Hall's marriage theorem and Tutte's
theorem) which we will discuss in
[Matchings](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-matchings).
But it does not (yet) define the *matching number* `ν G`: the maximum number of edges
in a matching of `G`. Following Mathlib's `SimpleGraph.vertexCoverNum`, we define it
as an indexed supremum in the extended naturals `ℕ∞`, measuring each matching with
`Set.encard`. So a graph with arbitrarily large matchings has matching number `⊤`. In
the definition below, the second binder `(_ : M.IsMatching)` ranges over proofs that
`M` is a matching, so a subgraph that is not a matching contributes an empty
supremum, `⊥ = 0`, and only matchings count.
-/
section matchingnumber
variable {V : Type*} {G : SimpleGraph V}

#check Set.encard
#source vertexCoverNum

/-!
We introduce the standard `τ G` notation for the vertex cover number.
-/
@[inherit_doc vertexCoverNum]
scoped notation "τ" => SimpleGraph.vertexCoverNum

/-- The *matching number* `ν G` of `G` is the maximum number of edges in a matching
of `G`, as an element of `ℕ∞` (so `⊤` if `G` has arbitrarily large matchings). -/
noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

/-!
We introduce the standard notation `ν G` for the matching number.
-/
@[inherit_doc matchingNum]
scoped notation "ν" => SimpleGraph.matchingNum
/-!
Whenever we make a new definition we should immediately prove the basic lemmas
that let us use it without unfolding it: its *API*. Because `ℕ∞` is a complete
lattice the indexed supremum always exists, with no nonemptiness or boundedness
side-condition to discharge (an `sSup`-in-`ℕ` definition would need both). The two
directions of the supremum are then immediate from the generic `iSup` API.
-/
/-!
Any matching gives a lower bound for the matching number.
-/
lemma Subgraph.IsMatching.le_matchingNum {M : G.Subgraph}
    (h : M.IsMatching) : M.edgeSet.encard ≤ ν G :=
  le_iSup₂ (f := fun (M : G.Subgraph) (_ : M.IsMatching) => M.edgeSet.encard) M h

/-!
To bound the matching number from above it suffices to bound the size of
every matching.
-/
lemma matchingNum_le {n : ℕ∞}
    (h : ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ n) : ν G ≤ n :=
  iSup₂_le h

/-!
The empty subgraph is a matching (vacuously, since it has no vertices), so the
supremum defining `ν G` is never over an empty family.
-/
lemma Subgraph.isMatching_bot : (⊥ : G.Subgraph).IsMatching :=
  fun _ hv => hv.elim

/-!
It is sometimes convenient to take the supremum over the subtype of matchings,
rather than over the doubly indexed family.
-/
lemma matchingNum_eq_iSup_subtype : ν G =
    ⨆ M : {M : G.Subgraph // M.IsMatching}, (M : G.Subgraph).edgeSet.encard :=
  iSup_subtype'

/-!
For a finite type `Set.encard` is just the coercion of `Set.ncard`, and Mathlib's
`Set.coe_ncard_eq_encard` records this. Rewriting with it right-to-left lets us
move matching sizes from `ℕ∞` down to `ℕ`, where we can do arithmetic.
-/
#check Set.coe_ncard_eq_encard

/-!
In a finite graph the supremum is attained by some matching. Completeness of `ℕ∞`
does not give this for free, but with `[Finite V]` there are only finitely many
subgraphs (`instance : Finite G.Subgraph`), so the supremum, taken over the finite
nonempty subtype of matchings, is a maximum (`exists_eq_ciSup_of_finite`).
(Mathematically, finiteness is not necessary here, but the proof when `ν G = ⊤` is
more involved, requiring either a greedy chain argument or Zorn's lemma. See the
exercises for details.)
-/
lemma exists_isMatching_matchingNum [Finite V] :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = ν G := by
  have : Nonempty {M : G.Subgraph // M.IsMatching} := ⟨⟨⊥, Subgraph.isMatching_bot⟩⟩
  obtain ⟨M, hM⟩ := exists_eq_ciSup_of_finite
    (f := fun x : {M : G.Subgraph // M.IsMatching} =>
      (x : G.Subgraph).edgeSet.encard)
  exact ⟨M, M.2, by rw [matchingNum_eq_iSup_subtype]; exact hM⟩

/-!
As a sanity check we show that the empty graph has matching number `0`: it has no
edges, so neither does any of its matchings. Note how our API keeps `iSup` out of
the proof.
-/
lemma matchingNum_bot : ν (⊥ : SimpleGraph V) = 0 :=
  nonpos_iff_eq_zero.mp <| matchingNum_le fun M _ => by
    simp [Set.subset_empty_iff.mp (edgeSet_bot ▸ M.edgeSet_subset)]

/-!
The edges of `M.coe`, a graph on `M.verts`, correspond to the edges of `M` itself
(`Subgraph.image_coe_edgeSet_coe`), so the two edge sets have the same size.
-/
lemma Subgraph.ncard_edgeSet_coe (M : G.Subgraph) :
    M.coe.edgeSet.ncard = M.edgeSet.ncard := by
  rw [← M.image_coe_edgeSet_coe,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

#check Subgraph.IsMatching.even_card
/-!
The number of vertices covered by a matching is twice its number of edges. (This is
the `Set.ncard` version of the degree-sum argument used by
`Subgraph.IsMatching.even_card`.)
-/
lemma Subgraph.IsMatching.ncard_verts [Finite V] {M : G.Subgraph}
    (h : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have hverts : M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
    trans Fintype.card M.verts
    · exact Set.toFinset_card M.verts
    · rw [← M.coe.sum_degrees_eq_twice_card_edges, ← Finset.card_univ,
          Finset.card_eq_sum_ones]
      congr with x
      rw [coe_degree, eq_comm, degree_eq_one_iff_existsUnique_adj]
      obtain ⟨w, hw, huniq⟩ := h x.2
      exact ⟨w, hw, fun y hy => huniq _ hy⟩
  rw [Set.ncard_eq_toFinset_card', hverts, ← M.ncard_edgeSet_coe,
    Set.ncard_eq_toFinset_card']
  rfl

/-!
If `p₁` is an independent set then every edge of a matching has at most one endpoint
in `p₁`. So a matching with finitely many edges has at least as many edges as it has
vertices in `p₁`: sending each such vertex to its edge in the matching is injective.
-/
lemma Subgraph.IsMatching.ncard_inter_le_of_isIndepSet {p₁ : Set V}
    (h₁ : G.IsIndepSet p₁) {M : G.Subgraph} [Finite M.edgeSet]
    (hM : M.IsMatching) :
    (p₁ ∩ M.verts).ncard ≤ M.edgeSet.ncard := by
  classical
  -- send each matched vertex to its edge in `M`
  refine Set.ncard_le_ncard_of_injOn
    (fun v => if hv : v ∈ M.verts then (hM.toEdge ⟨v, hv⟩ : Sym2 V) else s(v, v))
    (fun v hv => by simp [hv.2]) (fun x hx y hy hxy => ?_) (Set.toFinite _)
  by_contra hne
  -- `x` and `y` are sent to the same edge of `M`, so both lie on the edge at `y`
  have hxy' : (hM.toEdge ⟨x, hx.2⟩ : Sym2 V) = hM.toEdge ⟨y, hy.2⟩ := by
    simpa only [hx.2, hy.2, dite_true] using hxy
  have hxe : x ∈ (hM.toEdge ⟨y, hy.2⟩ : Sym2 V) := hxy' ▸ hM.mem_coe_toEdge hx.2
  have hye : y ∈ (hM.toEdge ⟨y, hy.2⟩ : Sym2 V) := hM.mem_coe_toEdge hy.2
  -- since `x ≠ y`, this edge must be `s(x, y)`
  have he : (hM.toEdge ⟨y, hy.2⟩ : Sym2 V) = s(x, y) :=
    (Sym2.mem_and_mem_iff hne).1 ⟨hxe, hye⟩
  -- so `x` and `y` are adjacent in `G`, contradicting the independence of `p₁`
  have hadj : G.Adj x y := by
    rw [← mem_edgeSet, ← he]
    exact M.edgeSet_subset (hM.toEdge ⟨y, hy.2⟩).2
  exact h₁ hx.1 hy.1 hne hadj

/-!
In particular, if `G` is bipartite with parts `p₁` and `p₂` (`IsBipartiteWith`) then
`p₁` is independent, so a matching with finitely many edges has at least as many
edges as it has vertices in `p₁`. We use this later in the proof of
[Kőnig's Theorem](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-k-nig-s-theorem).
-/
lemma Subgraph.IsMatching.ncard_inter_le {p₁ p₂ : Set V}
    (h₁ : G.IsBipartiteWith p₁ p₂) {M : G.Subgraph} [Finite M.edgeSet]
    (hM : M.IsMatching) :
    (p₁ ∩ M.verts).ncard ≤ M.edgeSet.ncard :=
  hM.ncard_inter_le_of_isIndepSet fun _ hx _ hy _ h =>
    Set.disjoint_left.1 h₁.disjoint hy (h₁.mem_of_mem_adj hx h)

/-!
A matching covers two vertices per edge, so the matching number of any finite graph
is at most `|V| / 2`.
-/
lemma matchingNum_le_card_div_two [Finite V] : ν G ≤ ↑(Nat.card V / 2) :=
  matchingNum_le fun N hN => by
    have := N.verts.ncard_le_card
    rw [← Set.coe_ncard_eq_encard, Nat.cast_le]
    grind [hN.ncard_verts]

/-!
If `G` has a perfect matching then this bound is attained: `ν G = |V| / 2`.
-/
lemma Subgraph.IsPerfectMatching.matchingNum_eq [Finite V] {M : G.Subgraph}
    (h : M.IsPerfectMatching) : ν G = ↑(Nat.card V / 2) := by
  -- The perfect matching covers all of `V`, so it has `|V| / 2` edges.
  have hcard : 2 * M.edgeSet.ncard = Nat.card V := by
    rw [← h.1.ncard_verts, h.2.verts_eq_univ, Set.ncard_univ]
  refine le_antisymm matchingNum_le_card_div_two (le_trans ?_ h.1.le_matchingNum)
  rw [← Set.coe_ncard_eq_encard, Nat.cast_le]
  grind

/-!
When `|V|` is even, the `|V| / 2` bound is tight exactly when `G` has a perfect
matching.

A second upper bound comes from vertex covers. *Weak duality* says that `ν G ≤ τ G`,
where `τ G` is the minimum size of a *vertex cover*, a set of vertices meeting every
edge: the edges of a matching are pairwise disjoint, so a vertex cover must contain a
distinct vertex from each of them. For *bipartite* graphs this is an equality
(*Kőnig's theorem*, which is not in Mathlib; we prove it in
[Kőnig's Theorem](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-k-nig-s-theorem)),
but it can be strict: the odd cycle `C[2 * k + 3]` has `ν = k + 1` and `τ = k + 2`.
(The exercises check the smallest case, `K[3]`.)

[Figure: Left: in $C_5$ a maximum matching (red) has $2$ edges, but a minimum vertex cover (green) needs $3$ vertices, so $\nu = 2 < 3 = \tau$. Right: in the bipartite graph $C_6$ the two are equal, $\nu = \tau = 3$](https://jt496.github.io/GraphTheoryInLean/figures/matching_cover.svg)

The proof of `ν G ≤ τ G` rests on two elementary facts, which we isolate as reusable
lemmas. The first says that a matching is *locally injective* on edges: since every
vertex of a matching is incident to a unique edge, two matching edges that share a
vertex must coincide.
-/
/-- In a matching, every vertex is incident to at most one edge: two edges of the
matching sharing a vertex are equal. -/
lemma Subgraph.IsMatching.eq_of_mem_edge {M : G.Subgraph} (hM : M.IsMatching)
    {e₁ e₂ : Sym2 V} (he₁ : e₁ ∈ M.edgeSet) (he₂ : e₂ ∈ M.edgeSet)
    {v : V} (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) : e₁ = e₂ := by
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp hv₁
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hv₂
  exact congrArg (s(v, ·)) (hM.eq_of_adj_left he₁ he₂)

/-!
The second is the defining property of a vertex cover: every edge of `G` contains one
of the cover's vertices.
-/
/-- Every edge of `G` meets any vertex cover `C`. -/
lemma IsVertexCover.exists_mem_edge {C : Set V} (hC : G.IsVertexCover C)
    {e : Sym2 V} (he : e ∈ G.edgeSet) : ∃ v ∈ e, v ∈ C := by
  induction e using Sym2.ind with
  | _ a b => simpa using hC he

/-!
Weak duality: the matching number of a graph is at most its vertex cover number.
-/
theorem matchingNum_le_vertexCoverNum (G : SimpleGraph V) :
    ν G ≤ τ G := by
  obtain ⟨C, hcard, hcover⟩ := G.vertexCoverNum_exists
  rw [← hcard]
  refine matchingNum_le fun M hM => ?_
  -- Each edge of the matching contains a vertex of the cover `C`.
  have hmem : ∀ e : M.edgeSet, ∃ v : C, (v : V) ∈ (e : Sym2 V) := fun e => by
    obtain ⟨v, hv, hvC⟩ := hcover.exists_mem_edge (M.edgeSet_subset e.2)
    exact ⟨⟨v, hvC⟩, hv⟩
  -- Sending each edge to a chosen cover vertex is an injection into `C`: distinct
  -- matching edges pick distinct vertices, by local injectivity of the matching.
  choose f hf using hmem
  exact ENat.card_le_card_of_injective (f := f) fun e₁ e₂ h =>
    Subtype.ext (hM.eq_of_mem_edge e₁.2 e₂.2 (hf e₁) (h ▸ hf e₂))


end matchingnumber
section hypercubematching
variable {V : Type*} {G : SimpleGraph V}
/-!
## Matching Number of the Hypercube

The hypercube `Q[n + 1]` has a natural *perfect matching*: pair each vertex with the
one obtained by flipping its first coordinate, so `v[0, …]` is matched with
`v[1, …]`. (Flipping the first coordinate rather than the last lets us build the
matching by recursion on `n`.)

Rather than reason about the hypercube directly, we isolate the underlying general
fact about box products: if `M` is a perfect matching of `G`, then copying `M` into
every `G`-fibre of `G □ H` is a perfect matching of `G □ H`, for any graph `H`, whose
edges play no role at all.
-/
/-- Copy a subgraph `M` of `G` into every `G`-fibre of `G □ H`: the vertex `(v, b)`
is present iff `v ∈ M.verts`, and `(a, b)` and `(c, b)` are adjacent iff `a` and `c`
are adjacent in `M`. This is the box product of `M` with the edgeless (but fully
spanning) subgraph on `H`. -/
@[simps]
def Subgraph.boxProdLeft {β : Type*} (M : G.Subgraph) (H : SimpleGraph β) :
    (G □ H).Subgraph where
  verts := {x | x.1 ∈ M.verts}
  Adj x y := M.Adj x.1 y.1 ∧ x.2 = y.2
  adj_sub h := boxProd_adj.2 (Or.inl ⟨M.adj_sub h.1, h.2⟩)
  edge_vert h := M.edge_vert h.1
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

/-!
If `M` is a perfect matching of `G` then `M.boxProdLeft H` is a perfect matching of
`G □ H`: the unique neighbour of `(v, b)` is `(w, b)`, where `w` is the `M`-partner
of `v`.
-/
lemma Subgraph.IsPerfectMatching.boxProdLeft {β : Type*} {M : G.Subgraph}
    (h : M.IsPerfectMatching) (H : SimpleGraph β) :
    (M.boxProdLeft H).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  rintro ⟨v, b⟩
  obtain ⟨w, hw, huniq⟩ := h.1 (h.2 v)
  refine ⟨(w, b), ⟨hw, rfl⟩, ?_⟩
  rintro ⟨c, d⟩ ⟨hadj, rfl⟩
  exact Prod.ext (huniq c hadj) rfl

/-!
The recursive perfect matching of the hypercube is now immediate.
-/
/-- A perfect matching of `Q[n + 1]` defined recursively: `⊤` on `Q[1]`, and on
`Q[n + 2]` the `Subgraph.boxProdLeft` of `hypercube.matching n` along `K₂`. -/
def hypercube.matching : (n : ℕ) → Q[n + 1].Subgraph
  | 0 => ⊤
  | n + 1 => (hypercube.matching n).boxProdLeft ⊤

/-!
A graph, or rather its `top` subgraph, is a perfect matching iff every vertex has
degree one.
-/
lemma Subgraph.isPerfectMatching_top_iff [G.LocallyFinite] :
    (⊤ : G.Subgraph).IsPerfectMatching ↔ ∀ v : V, G.degree v = 1 := by
  simp [isPerfectMatching_iff, SimpleGraph.degree_eq_one_iff_existsUnique_adj]

/-!
By induction `hypercube.matching n` is a perfect matching of `Q[n + 1]`.
-/
lemma hypercube.matching_isPerfectMatching :
    ∀ n : ℕ, (hypercube.matching n).IsPerfectMatching
  | 0 => Subgraph.isPerfectMatching_top_iff.mpr <| hypercube_isRegularOfDegree _
  | n + 1 => (hypercube.matching_isPerfectMatching n).boxProdLeft ⊤

/-!
Since `Q[n + 1]` has `2 ^ (n + 1)` vertices, this perfect matching gives
`ν Q[n + 1] = 2 ^ n`.
-/
lemma matchingNum_hypercube_succ (n : ℕ) : ν Q[n + 1] = 2 ^ n := by
  rw [(hypercube.matching_isPerfectMatching n).matchingNum_eq]
  have h : Nat.card (HypercubeVert (n + 1)) / 2 = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, card_hypercubeVert, pow_succ]; grind
  exact_mod_cast h

end hypercubematching
/-!
## Matching Number of the Mycielskian

If `M` is a matching in `G` then we can construct a matching in the Mycielskian
`mμ[G]` by taking the edges `x ₗ — y ᵣ` and `x ᵣ — y ₗ` for each edge `x — y` in `M`.
This makes sense for any subgraph `M` of `G` (although it won't be a matching in
general).
-/
section mycielskian
variable {V : Type*} {G : SimpleGraph V}
/-- Given a subgraph `M` of `G`, the `mycielskianDouble` of `M` is the subgraph of
`mμ[G]` with edges given by `x ₗ — y ᵣ` and `x ᵣ — y ₗ` for each edge `x — y` in `M`.
-/
@[simps]
def Subgraph.mycielskianDouble (M : G.Subgraph) : Subgraph mμ[G] where
  verts := (· ₗ) '' M.verts ∪ (· ᵣ) '' M.verts
  Adj a b := ∃ x y, M.Adj x y ∧ ((a = x ₗ ∧ b = y ᵣ) ∨ (a = x ᵣ ∧ b = y ₗ))
  adj_sub := by
    rintro a b ⟨x, y, hxy, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> exact M.adj_sub hxy
  edge_vert := by grind [M.edge_vert]
  symm := ⟨by grind [Adj.symm]⟩

/-!
The `mycielskianDouble` of a matching is a matching: each vertex in the left copy
of the vertices of `M` is matched with the right copy of its match in `M`.
-/
lemma Subgraph.IsMatching.mycielskianDouble {M : G.Subgraph}
    (h : M.IsMatching) : M.mycielskianDouble.IsMatching := by
  rintro a (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> obtain ⟨y, hxy, huniq⟩ := h hx
  · -- `a = x ₗ`: its unique neighbour is `y ᵣ`, where `y` is the `M`-partner of `x`.
    refine ⟨y ᵣ, ⟨x, y, hxy, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨x', y', hx'y', (⟨hl, rfl⟩ | ⟨hl, rfl⟩)⟩ <;> simp_all
  · -- `a = x ᵣ`: its unique neighbour is `y ₗ`.
    refine ⟨y ₗ, ⟨x, y, hxy, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro w ⟨x', y', hx'y', (⟨hl, rfl⟩ | ⟨hl, rfl⟩)⟩ <;> simp_all

/-- The embedding of the darts of a subgraph into the edge set of its Mycielskian
double. -/
def Subgraph.mycielskianDoubleDartEmbedding (M : G.Subgraph) :
    M.coe.Dart ↪ (M.mycielskianDouble).edgeSet where
  toFun d := ⟨s(d.1.1.val ₗ, d.1.2.val ᵣ), by
    simp only [Subgraph.mem_edgeSet, Subgraph.mycielskianDouble]
    exact ⟨d.1.1.val, d.1.2.val, d.adj, Or.inl ⟨rfl, rfl⟩⟩⟩
  inj' d₁ d₂ h := by ext <;> simp_all

/-!
Each dart of `M` gives a distinct edge of `M.mycielskianDouble`, and a finite
graph has twice as many darts as edges, so the double has at least twice as many
edges as `M`. Counting darts is a `Fintype` computation, so we do it in `ℕ` with
`Nat.card` and only cast up to `ℕ∞` at the end.
-/
lemma Subgraph.two_mul_edgeSet_encard_le_mycielskianDouble [Finite V]
    (M : G.Subgraph) :
    2 * M.edgeSet.encard ≤ (M.mycielskianDouble).edgeSet.encard := by
  classical
  have := Fintype.ofFinite V
  -- Each edge of `M` gives two darts, so `M.coe` has `2 * |E(M)|` darts.
  have hdart : Nat.card M.coe.Dart = 2 * M.edgeSet.ncard := by
    rw [Nat.card_eq_fintype_card, dart_card_eq_twice_card_edges,
      ← M.ncard_edgeSet_coe, Set.ncard_eq_toFinset_card']
    rfl
  have hle : Nat.card M.coe.Dart ≤ Nat.card (M.mycielskianDouble).edgeSet :=
    Nat.card_le_card_of_injective _ M.mycielskianDoubleDartEmbedding.injective
  rw [hdart, Nat.card_coe_set_eq] at hle
  -- Move the `ℕ` inequality up to `ℕ∞`.
  rw [← Set.coe_ncard_eq_encard, ← Set.coe_ncard_eq_encard]
  exact_mod_cast hle

/-!
The matching number of the Mycielskian of `G` is at least twice the matching number
of `G`.
-/
lemma two_mul_matchingNum_le_matchingNum_mycielskian [Finite V] :
    2 * ν G ≤ ν mμ[G] := by
  obtain ⟨M, hM, hc⟩ := exists_isMatching_matchingNum (G := G)
  calc
    2 * ν G = 2 * M.edgeSet.encard := by rw [hc]
    _ ≤ (M.mycielskianDouble).edgeSet.encard :=
        two_mul_edgeSet_encard_le_mycielskianDouble M
    _ ≤ ν mμ[G] := hM.mycielskianDouble.le_matchingNum

/-!
When `G` has a perfect matching the lower bound `2 * ν G` is exact: the Mycielskian
has `2 * |V| + 1` vertices, so by `matchingNum_le_card_div_two` no matching of
`mμ[G]` can have more than `|V| = 2 * ν G` edges.

(For graphs without a perfect matching the lower bound `2 * ν G` can be far from
exact. If `G` is a disjoint union of two triangles it has matching number `2`, but
the cross edges `a ₗ — b ᵣ`, `b ₗ — c ᵣ`, `c ₗ — a ᵣ` of each triangle form a
matching of size `6` in the Mycielskian.)
-/
lemma Subgraph.IsPerfectMatching.matchingNum_mycielskian_eq [Finite V]
    {M : G.Subgraph} (h : M.IsPerfectMatching) : ν mμ[G] = 2 * ν G := by
  classical
  have := Fintype.ofFinite V
  -- A graph with a perfect matching has an even number of vertices.
  obtain ⟨k, hk⟩ : Even (Nat.card V) := by
    simpa [Nat.card_eq_fintype_card] using h.even_card
  -- The Mycielskian has `2 * |V| + 1` vertices.
  have hcard : Nat.card (Option (V ⊕ V)) = 2 * Nat.card V + 1 := by
    grind [card_mycielskianVert_one, ← Nat.card_eq_fintype_card]
  -- `2 * ν G = |V|` in `ℕ∞`, since `ν G = |V| / 2` and `|V|` is even.
  have h2ν : 2 * ν G = (Nat.card V : ℕ∞) := by
    rw [h.matchingNum_eq]; norm_cast; grind
  -- The upper bound `ν mμ[G] ≤ (2|V|+1)/2 = |V|` meets the lower bound `2 * ν G`.
  refine le_antisymm ((matchingNum_le_card_div_two (G := mμ[G])).trans ?_)
    two_mul_matchingNum_le_matchingNum_mycielskian
  rw [h2ν, Nat.cast_le]
  grind

end mycielskian

/-!
# Partial Colourings *

Informally, a *partial `γ`-colouring* of `G : SimpleGraph V` should be a map
`C : V → γ` that is valid on a given subset of the vertices `s : Set V`, where valid
means something like `∀ a b ∈ s, G.Adj a b → C a ≠ C b`.

There is currently no definition of partial colourings in Mathlib. However they arise
in many situations, such as the proof of Brooks' theorem. (Indeed we will use them
for exactly this; see
[Brooks' Theorem*](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-brooks-theorem).)

Below we discuss a possible implementation making use of the existing
`SimpleGraph.Coloring` API where possible.

We want a partial colouring `C` to be a total function on `V` and we also want to
reuse the `SimpleGraph.Coloring` API. The natural way to implement this is as a
colouring of the subgraph of `G` induced by `s` but with all vertices of `V`
retained: i.e. a colouring of `(G.induce s).spanningCoe`, where `spanningCoe` is
`SimpleGraph.spanningCoe` from
[SpanningCoe](https://jt496.github.io/GraphTheoryInLean/Maps/#section-spanningcoe).
Alternatively we could ask for `C` to be a colouring of
`((⊤ : G.Subgraph).induce s).spanningCoe`, using `Subgraph.spanningCoe` instead.

These are the same graph (this is Mathlib's `spanningCoe_induce_top`), but they are
not *definitionally* equal
([Definitional and Propositional Equalities](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-definitional-and-propositional-equalities)),
and the latter is much easier to work with. Its adjacency relation is definitionally
`a ∈ s ∧ b ∈ s ∧ G.Adj a b`. While in `(G.induce s).spanningCoe`, adjacency unfolds
to an existential over vertices of the subtype `↑s`, coming from `SimpleGraph.map`:
`a ≠ b ∧ ∃ u v : ↑s, (G.induce s).Adj u v ∧ ↑u = a ∧ ↑v = b`.
-/
section partcol
variable {V : Type*} {G : SimpleGraph V}
example {s : Set V} :
    ((⊤ : G.Subgraph).induce s).spanningCoe = (G.induce s).spanningCoe :=
  spanningCoe_induce_top _

example {a b : V} {s : Set V} :
    ((⊤ : G.Subgraph).induce s).spanningCoe.Adj a b ↔ a ∈ s ∧ b ∈ s ∧ G.Adj a b :=
  Iff.rfl

example {a b : V} {s : Set V} :
    (G.induce s).spanningCoe.Adj a b ↔
      a ≠ b ∧ ∃ u v : ↑s, (G.induce s).Adj u v ∧ ↑u = a ∧ ↑v = b := Iff.rfl

variable (G)
/-- A `ColoringOn γ s` of `G : SimpleGraph V` is a `γ`-colouring of all vertices of
`G` that is a valid colouring on the set `s`. -/
abbrev ColoringOn (γ : Type*) (s : Set V) :=
  ((⊤ : G.Subgraph).induce s).spanningCoe.Coloring γ

/-- `G.ColorableOn n s` iff there is a total function `V → Fin n` that is a valid
colouring of `G` on the set `s`. -/
abbrev ColorableOn (n : ℕ) (s : Set V) := Nonempty (G.ColoringOn (Fin n) s)

variable {s t : Set V} {γ : Type*} {G}
/-!
## Restricting and Copying Partial Colourings

A partial colouring of `s` can be *restricted* to any subset `t ⊆ s`: we use the same
function and note that the validity condition holds for the subset. We call this
`ColoringOn.restrict`.
-/
/-- Restrict `C : G.ColoringOn γ s` to any `t ⊆ s`. -/
@[simps]
protected def ColoringOn.restrict (C : G.ColoringOn γ s) (h : t ⊆ s) :
    G.ColoringOn γ t where
  toFun := C
  map_rel' := fun ⟨ha, hb, hab⟩ ↦ C.valid ⟨h ha, h hb, hab⟩

/-!
Notice that whereas `Walk.copy` was the cast `hu ▸ hv ▸ p`, which is stuck until we
substitute the endpoints, here we reuse the underlying function `C` unchanged and
discharge the validity condition directly: an edge of the subgraph induced by `t` is
an edge of the subgraph induced by `s`, so `C.valid` applies. Because the underlying
function is untouched, a restriction agrees with the original at every vertex, by
`rfl` and with no substitution needed. The `@[simps]` attribute records this as the
`simp` lemma `restrict_apply`, which lets `simp` rewrite `(C.restrict h) v` to `C v`
automatically, so downstream proofs need not unfold restrictions by hand.
-/
#check ColoringOn.restrict_apply -- (C.restrict h) a = C a

/-!
In practice the most common use of `restrict` is the trivial one where the subset is
equal to the original set. `ColoringOn` is a type that encodes data, and just as with
`Walk.copy` we frequently need to change the set on which a colouring is valid to one
that is equal but not definitionally equal to it, for example `↑(insert a s)` versus
`insert a ↑s`. This is the idea behind the *range copy pattern* from
[Plumbing Elsewhere in the API](https://jt496.github.io/GraphTheoryInLean/Walks/#section-plumbing-elsewhere-in-the-api),
applied, as for `Walk.copy`, to data in the type rather than in a field, and it is
just restriction along `h.ge : t ⊆ s`. We call this `ColoringOn.copy`. (Mathlib's
`Subgraph.copy` is an instance of the pattern itself: it replaces the `verts` and
`Adj` fields of a subgraph by propositionally equal ones.)
-/
#check Subgraph.copy

/-- Construct a `G.ColoringOn γ t` from `C : G.ColoringOn γ s` and a proof that
`s = t`. -/
@[simps!]
protected def ColoringOn.copy (C : G.ColoringOn γ s) (h : s = t) :
    G.ColoringOn γ t :=
  C.restrict h.ge

/-!
The body of `copy` is an application of `restrict` rather than a structure, so we
need `@[simps!]` to unfold it. The generated `simp` lemma `copy_apply` also serves
as a named lemma for the explicit `rw` chains that step through a copy to expose the
underlying `union`/`insert`.
-/
#check ColoringOn.copy_apply -- (C.copy h) a = C a

/-!
By far the most common source of such mismatches for us will be due to the coercion
from `Finset V` to `Set V`. Following the Mathlib convention that definitions are
made for the more general type, our basic constructors are stated for `Set V`. In
practice, however, we almost always colour finite sets. When we pass `ColoringOn` a
`Finset V` it is automatically coerced to a `Set V` (since `Finset` has a `SetLike`
instance). Depending on how this coercion is applied we may end up with a type
mismatch that we will need to fix with `copy`.

For example, we might end up with a colouring of `↑s ∪ ↑t` (the `Set V` given by
coercing each of `s t : Finset V` to `Set V` and then taking their union) when the
goal asks for a colouring of `↑(s ∪ t)` (the coercion of the `Finset V` that is the
`Finset` union of `s` and `t`). These two sets are obviously equal but the proof
is not `rfl` (it is the `simp` lemma `Finset.coe_union`).
-/
/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (s t : Finset V) [DecidableEq V] (C : G.ColoringOn γ (↑s ∪ ↑t)) :
    G.ColoringOn γ ↑(s ∪ t) := C

example (s t : Finset V) [DecidableEq V] (C : G.ColoringOn γ (↑s ∪ ↑t)) :
    G.ColoringOn γ ↑(s ∪ t) := C.copy (by simp)

/-!
For this reason we will need to use `copy` frequently in proofs. Fortunately
`Finset.coe_insert`, `Finset.coe_union`, `Finset.coe_empty` etc. are all `simp`
lemmas, so the proof obligation that `copy` requires will almost always be discharged
by `simp`.
-/
#check Finset.coe_empty  -- ((∅ : Finset α) : Set α) = ∅
#check Finset.coe_insert -- ↑(insert a s) = insert a ↑s
#check Finset.coe_union  -- ↑(s₁ ∪ s₂) = ↑s₁ ∪ ↑s₂

/-!
## Building Partial Colourings

Fundamentally we are interested in partial colourings as a tool to build total
colourings, so we want to be able to turn a `G.ColoringOn γ Set.univ` into a
`G.Coloring γ`.
-/
/-- A `G.ColoringOn γ Set.univ` is a `G.Coloring γ`. -/
@[simps]
def ColoringOn.toColoring (C : G.ColoringOn γ Set.univ) : G.Coloring γ :=
    ⟨C, fun h ↦ C.valid (by simpa using h)⟩

/-- A colouring gives rise to a partial colouring on any set. -/
@[simps]
def Coloring.toColoringOn (C : G.Coloring γ) (s : Set V) : G.ColoringOn γ s :=
    ⟨C, fun h ↦ C.valid (by simpa using h.2.2)⟩

/-!
A graph is `n`-colourable if and only if `G.ColorableOn n Set.univ`.
-/
variable (G)
lemma colorableOn_univ_iff_colorable (n : ℕ) :
    G.ColorableOn n (Set.univ : Set V) ↔ G.Colorable n := by
  constructor <;> intro ⟨c⟩
  · exact ⟨c.toColoring⟩
  · exact ⟨c.toColoringOn _⟩

/-!
There are a few basic partial colourings that we will need to construct: the partial
colouring of the empty set, the partial colouring of a singleton, and the partial
colouring of a pair of non-adjacent vertices.
-/

/-- The partial colouring of the empty set by a colour `c`. -/
@[simps!]
def coloringOnEmpty (c : γ) : G.ColoringOn γ ∅ :=
  Coloring.mk (fun _ => c) fun h => h.1.elim


/-- The partial colouring of the singleton set `{a}` by a colour `c`. -/
@[simps]
def coloringOnOfSingleton {γ : Type*} (a : V) (c : γ) :
    G.ColoringOn γ {a} where
  toFun := fun _ ↦ c
  map_rel' := by simp

/-- The partial colouring of a pair of non-adjacent vertices by a colour `c`. -/
@[simps]
def coloringOnOfNotAdj {γ : Type*} {a b : V} (h : ¬ G.Adj a b) (c : γ) :
    G.ColoringOn γ {a, b} where
  toFun := fun _ ↦ c
  map_rel' := by
    rintro x y ⟨hx, hy, hxy⟩ -
    grind [adj_comm]

variable {G}
/-!
We can combine two partial colourings by extending the first using the second,
provided they are compatible in the sense that there is no edge between a vertex
coloured by `C₁` and a vertex coloured only by `C₂` using the same colour. This gives
a partial colouring on the union of the two sets.
-/
/-- We can combine colourings `C₁` of `s` and `C₂` of `t` if they are compatible,
i.e. `∀ v w, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w` to get a colouring of
`s ∪ t`. It agrees with `C₁` on `s` and with `C₂` on `t \ s`. -/
@[simps]
def ColoringOn.union [DecidablePred (· ∈ s)] (C₁ : G.ColoringOn γ s)
    (C₂ : G.ColoringOn γ t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
    G.ColoringOn γ (s ∪ t) where
  toFun := fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)
  map_rel' := by
    rintro v w ⟨hv', hw', hadj⟩ hf
    split_ifs at hf with hv hw hw
    · exact C₁.valid ⟨hv, hw, hadj⟩ hf
    · exact h hv ⟨hw'.resolve_left hw, hw⟩ hadj hf
    · exact h hw ⟨hv'.resolve_left hv, hv⟩ hadj.symm hf.symm
    · exact C₂.valid ⟨hv'.resolve_left hv, hw'.resolve_left hw, hadj⟩ hf

#check ColoringOn.union_apply -- (C₁.union C₂ h) v = if v ∈ s then C₁ v else C₂ v

/-!
Next we extend a colouring `C` of `s` to `insert x s` using a colour `c` that is not
used by `C` to colour a neighbour of `x` in `s`. We could build this as
`(G.coloringOnOfSingleton x c).union C _`, followed by a `copy` from `{x} ∪ s` to
`insert x s`, but then `@[simps!]` would only unfold it as far as that `union`.
Instead we define it directly, with the same four cases in the validity proof as for
`union`, and `@[simps]` then generates exactly the lemma we want.
-/
/-- Extend `C : G.ColoringOn γ s` to `insert x s` by colouring `x` with a colour `c`
that `C` does not use on any neighbour of `x` in `s`. -/
@[simps]
protected def ColoringOn.insert [DecidableEq V] (x : V) {c : γ}
    (C : G.ColoringOn γ s) (h : ∀ ⦃v⦄, v ∈ s → G.Adj x v → C v ≠ c) :
    G.ColoringOn γ (insert x s) where
  toFun v := if v = x then c else C v
  map_rel' := by
    rintro v w ⟨hv, hw, hadj⟩ hf
    split_ifs at hf with hvx hwx hwx
    · exact hadj.ne (hvx.trans hwx.symm)
    · exact h (hw.resolve_left hwx) (hvx ▸ hadj) hf.symm
    · exact h (hv.resolve_left hvx) (hwx ▸ hadj.symm) hf
    · exact C.valid ⟨hv.resolve_left hvx, hw.resolve_left hwx, hadj⟩ hf

/-!
So `C.insert x h` colours `x` with `c` and agrees with `C` elsewhere.
-/
#check ColoringOn.insert_apply -- (C.insert x h) v = if v = x then c else C v

/-!
Finally we can relabel the colours of a partial colouring along any injective map (in
particular along any permutation of the colours): validity is preserved, since an
injection cannot merge two distinct colours.
-/
/-- Relabel the colours of a partial colouring along an embedding. -/
@[simps!]
def ColoringOn.map {β : Type*} (f : γ ↪ β) (C : G.ColoringOn γ s) :
    G.ColoringOn β s :=
  (Embedding.completeGraph f).toHom.comp C

#check ColoringOn.map_apply --  (ColoringOn.map f C) x = f (C x)

end partcol
end SimpleGraph
