import GraphTheoryInLean.C07_Colorings.C07_Colorings
import GraphTheoryInLean.C08_Walks.C08_Walks
import GraphTheoryInLean.C09_Subgraphs.C09_Subgraphs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import GraphTheoryInLean.C08_Walks.Exercises
variable {V : Type*} {G : SimpleGraph V}
namespace SimpleGraph

open Walk

/-!
A graph is *connected* if it has at least one vertex and there is a walk between
every pair of vertices.

In this chapter we study graph connectivity. Building on the reachability relation of
[Reachability](https://jt496.github.io/GraphTheoryInLean/Walks/#section-reachability),
we start with Mathlib's notions `Preconnected` and `Connected`, connected components
and bridges, and show that the Mycielskian `mμ[G]` is connected iff `G` has no
isolated vertices. We then look at trees, and show that the infinite path `pathNat₁`
is one. We show that a graph is bipartite iff it has no cycle of odd length, and that
in a graph of maximum degree at most `2` every cycle runs through its whole
component. We prove *Euler's theorem*: a finite graph with at least one vertex has an
Eulerian trail iff all its edges lie in one component and it has either no vertex of
odd degree or exactly two. We then turn to Mathlib's edge connectivity
(`IsEdgeConnected`), define vertex connectivity (`IsVertexConnected`), and prove that
a `k`-vertex-connected graph is `k`-edge-connected and that the `n`-dimensional
hypercube `Q[n]` is both. This gives the inequality `κ(G) ≤ λ(G)` between the vertex
and edge connectivity numbers.

The final two sections are more advanced. We prove *Brooks' theorem*: a finite graph
of maximum degree at most `Δ` is `Δ`-colourable unless it contains a
`(Δ + 1)`-clique or (when `Δ = 2`) one of its components is an odd cycle. Then we
define the *blocks* of a graph as the classes of an equivalence relation on edges,
building our own quotient type just as Mathlib builds `ConnectedComponent`, and prove
that, for `n ≥ 1`, a finite graph is `n`-colourable if each of its blocks is.


# Connectivity

In Mathlib connectedness is defined in two steps: a graph is *preconnected* if there
is a walk between every pair of vertices, and a graph is *connected* if it is
preconnected and nonempty.

Recall from
[Reachability](https://jt496.github.io/GraphTheoryInLean/Walks/#section-reachability)
that, for a single pair of vertices `u v : V`, `G.Reachable u v` means that there is
a walk from `u` to `v`.
-/
#source Preconnected  -- def Preconnected : Prop := ∀ u v : V, G.Reachable u v
#source Connected -- structure Connected : Prop where
                  --   protected preconnected : G.Preconnected
                  --   protected [nonempty : Nonempty V]

/-!
## Connected Graphs

The two notions differ only for the graph on an empty vertex type. This graph is
vacuously preconnected, but it is not connected. With this convention a graph is
connected exactly when it has precisely one connected component; the empty graph has
none.
-/
example (h : G.Connected) {u v : V} : G.Reachable u v := h.preconnected u v

example (h : G.Connected) : Nonempty V := h.nonempty

example : (⊥ : SimpleGraph Empty).Preconnected := fun u => u.elim
example : ¬ (⊥ : SimpleGraph Empty).Connected := fun h => h.nonempty.some.elim

/-!
Notice that rather than having to write `h.preconnected u v` for `G.Reachable u v`
(where `h : G.Connected`) there is a `CoeFun` instance that lets us write the more
succinct `h u v`:
-/
#check instCoeFunConnectedForallForallReachable
example (h : G.Connected) {u v : V} : G.Reachable u v := h u v

/-!
The hypercube is connected: we can use the Hamming path to walk between any two
vertices, and we already gave a `Nonempty` instance for its vertices.
-/
lemma hypercube_connected (n : ℕ) : Q[n].Connected where
  preconnected := fun u v => ⟨u.hammingPath v⟩

/-!
For a concrete finite graph with decidable adjacency, connectivity is decidable, so
`decide` can check it (see
[Evaluating and Deciding](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-evaluating-and-deciding)).
-/
example : C[5].Connected := by decide

/-!
We have already met one source of connected graphs: a Hamiltonian graph is connected,
since a Hamiltonian cycle passes through every vertex
([Hamiltonian Paths and Cycles](https://jt496.github.io/GraphTheoryInLean/Walks/#section-hamiltonian-paths-and-cycles)).
-/
#check IsHamiltonian.connected

/-!
A connected graph has a path between any two vertices
-/
#check Connected.exists_isPath

/-!
A graph is connected iff there is a vertex `v` from which every other vertex is
reachable.
-/
#check connected_iff_exists_forall_reachable

/-!
A vertex is *isolated* if it has no neighbours.
-/
#source IsIsolated

/-!
In the Mycielskian of a graph `G`, any vertex `u` that is not isolated in `G` has
both its left and right copies in `mμ[G]` connected to `none`. Given the edge `u — v`
in `G` we have the walks `u ᵣ — none` and `u ₗ — v ᵣ — none` in `mμ[G]`.

Conversely if `u` is an isolated vertex in `G` then `u ₗ` is an isolated vertex in
`mμ[G]`.

Hence `mμ[G]` is connected iff `G` has no isolated vertices.
-/
theorem connected_mycielskian_iff : mμ[G].Connected ↔ ∀ v, ¬ G.IsIsolated v := by
  simp only [IsIsolated, not_forall, not_not]
  constructor <;> intro h
  · intro v
    obtain ⟨p⟩ := h.preconnected v ₗ none
    cases p; grind [mycielskian_adj]
  · apply (connected_iff_exists_forall_reachable _).2 ⟨none, fun z => ?_⟩
    rcases z with (_ | ⟨v | v⟩)
    · rfl
    · obtain ⟨u, h⟩ := h v
      exact (by simp : mμ[G].Adj _ _).reachable.trans
            (by simpa using h.symm : mμ[G].Adj u ᵣ _).reachable
    · exact (by simp : mμ[G].Adj _ _).reachable

/-!
## Connected Components

The *connected components* of `G` are the equivalence classes of `Reachable`.

[Figure: A graph with three connected components](https://jt496.github.io/GraphTheoryInLean/figures/connected_components.svg)
-/

#source ConnectedComponent -- def ConnectedComponent := Quot G.Reachable

/-!
The component containing a given vertex.
-/
#check G.connectedComponentMk  -- G.connectedComponentMk : V → G.ConnectedComponent

/-!
We introduce the notation `G⟦v⟧` for the connected component of `G` containing the
vertex `v`.
-/
@[inherit_doc connectedComponentMk]
scoped notation:max G "⟦" v "⟧" => SimpleGraph.connectedComponentMk G v

/-!
Two components are equal iff they are constructed from reachable vertices
-/
#check ConnectedComponent.eq

/-!
If we want to prove a fact about all components of a graph then we can use
`ConnectedComponent.ind` which says that to prove `β c` holds, for all components
`c`, it is sufficient to prove `β G⟦v⟧` for all vertices `v`.
-/
#check ConnectedComponent.ind

/-!
If a pair of vertices are adjacent then they are in the same component.
-/
#check ConnectedComponent.connectedComponentMk_eq_of_adj

/-!
For a finite graph with decidable adjacency, `G.ConnectedComponent` is a `Fintype`,
so we can count the components. The empty graph `⊥` on `Fin 3` has three, while
`C[5]` has one.
-/
#eval Fintype.card (⊥ : SimpleGraph (Fin 3)).ConnectedComponent -- 3
#eval Fintype.card C[5].ConnectedComponent -- 1

/-!
A connected graph has exactly one component: Mathlib's
`Preconnected.subsingleton_connectedComponent` says that there is at most one, and a
connected graph is nonempty, so there is at least one.
-/
lemma Connected.card_connectedComponent [Fintype G.ConnectedComponent]
    (h : G.Connected) : Fintype.card G.ConnectedComponent = 1 := by
  have := h.preconnected.subsingleton_connectedComponent
  have := h.nonempty.map G.connectedComponentMk
  exact le_antisymm (Fintype.card_le_one_iff_subsingleton.2 ‹_›) Fintype.card_pos

/-!
In informal graph theory we often think of a connected component as a graph, subgraph
or subset of the vertex set of the original graph. But in Lean a connected component
`C : G.ConnectedComponent` is none of these: it is an element of the *quotient type*
`G.ConnectedComponent` of `V` by the equivalence relation `Reachable`, that is, an
equivalence class of vertices. However we can convert a connected component into all
of these things.

The *support* of a component is the set of vertices in that component.
-/
#check ConnectedComponent.supp --  (C : G.ConnectedComponent) : Set V
/-!
The `SimpleGraph` and `Subgraph` given by a component are `c.toSimpleGraph` and
`c.toSubgraph`.
-/
#source ConnectedComponent.toSimpleGraph -- .. SimpleGraph C := G.induce C.supp
#source ConnectedComponent.toSubgraph -- .. G.Subgraph := Subgraph.induce ⊤ C.supp

/-!
Connectivity of a `G.Subgraph` is a separate notion, defined via the coercion of the
subgraph to a `SimpleGraph` on its vertex set. This is one of the duplications
discussed in
[Duplication](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-duplication);
we will use it in the proof of Brooks' theorem. The subgraph given by a component is
connected.
-/
#source Subgraph.Connected
#check ConnectedComponent.connected_toSubgraph

/-!
A set of vertices is maximal with respect to inducing a connected graph iff it is the
support of a component.
-/
#check ConnectedComponent.maximal_connected_induce_iff

/-!
When proving, for example, that a graph is bipartite it is standard to say "we just
need to 2-colour each component" since if we have 2-colourings for each component of
a graph we can combine them into a 2-colouring of the whole graph. This is more
generally true for homomorphisms.
-/
#check homOfConnectedComponents
/-!
Recall our definition of a `sigma` graph from
[Sum and Sigma Graphs*](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-sum-and-sigma-graphs):
the disjoint union of an indexed family of graphs.
-/
#check SimpleGraph.sigma
/-!
There is a natural isomorphism between a graph and the sigma graph of its connected
components. Informally this is obvious, but in Lean there is a subtlety. A vertex of
the sigma graph is a pair `⟨C, w⟩`, where the *type* of `w` (a vertex of
`C.toSimpleGraph`, that is, an element of the subtype `C.supp`) depends on the
component `C`. So two vertices `⟨C, v⟩` and `⟨D, w⟩` are adjacent when there is a
proof `h : C = D` and `v` is adjacent to `w` transported back along `h` (written
`h ▸ w`). In the proof below we generalize the component `D`, so that `rintro rfl`
can substitute `h` away, after which the transport is the identity.
-/
/-- The isomorphism between `G` and the sigma graph of its connected components -/
def isoSigmaConnectedComponents :
    G ≃g Σg (fun C : G.ConnectedComponent => C.toSimpleGraph) where
  toFun v := ⟨G⟦v⟧, ⟨v, rfl⟩⟩
  invFun p := p.2
  left_inv v := rfl
  right_inv := by
    -- matching the membership proof with `rfl` forces the component to be `G⟦v⟧`
    rintro ⟨_, ⟨v, rfl⟩⟩
    rfl
  map_rel_iff' {v w} := by
    have key : ∀ (D : G.ConnectedComponent) (h : G⟦v⟧ = D) (hw : w ∈ D),
        G⟦v⟧.toSimpleGraph.Adj ⟨v, rfl⟩ (h ▸ ⟨w, hw⟩) ↔ G.Adj v w := by
      rintro D rfl hw; exact ConnectedComponent.toSimpleGraph_adj _ rfl hw
    -- adjacent vertices lie in the same component
    have hc := @ConnectedComponent.connectedComponentMk_eq_of_adj _ G v w
    exact ⟨fun ⟨h, hadj⟩ => (key _ h _).mp hadj,
      fun h => ⟨hc h, (key _ (hc h) rfl).mpr h⟩⟩

/-!
## Bridges

An edge `e` is a *bridge* if deleting it disconnects its two endpoints from each
other.

[Figure: A graph with its bridge edges highlighted](https://jt496.github.io/GraphTheoryInLean/figures/bridges.svg)
-/

#source SimpleGraph.IsBridge

/-!
An edge of the graph `G` is a bridge iff it is not contained in any cycle in `G`.
-/
#check isBridge_iff_forall_cycle_notMem

/-!
Recall from
[Walks in the Mycielskian](https://jt496.github.io/GraphTheoryInLean/Walks/#section-walks-in-the-mycielskian)
that any edge `u — v` in a graph gives rise to a 5-cycle in its Mycielskian.
-/
#check isCycle_mycielskianClosed_of_adj

/-!
So every edge of `mμ[G]` that comes from an edge of `G` lies on a 5-cycle, and so
does the edge `none — u ᵣ` whenever `u` has a neighbour `v` in `G`. None of these
edges is a bridge. On the other hand, if `u` is isolated in `G` then `none` is the
only neighbour of `u ᵣ`, so deleting the edge `none — u ᵣ` cuts `u ᵣ` off. Hence the
bridges of `mμ[G]` are precisely the edges `none — u ᵣ` where `u` is an isolated
vertex of `G`.

[Figure: A graph and its Mycielskian with a unique bridge edge](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_bridge.svg)
-/

lemma isBridge_mycielskian_iff {e} (he : e ∈ mμ[G].edgeSet) :
    mμ[G].IsBridge e ↔ ∃ u, G.IsIsolated u ∧ e = s(none, u ᵣ) := by
  refine ⟨fun h => ?_, ?_⟩
  · -- `hncyc`: the bridge `e` lies on no cycle of `mμ[G]`
    have hncyc : ∀ ⦃u⦄ ⦃p : mμ[G].Walk u u⦄, p.IsCycle → e ∉ p.edges :=
      fun _ _ hp => h.notMem_edges_of_isCycle hp
    induction e using Sym2.ind with
    | h x y =>
      have hxy : mμ[G].Adj x y := mμ[G].mem_edgeSet.mp he
      rcases x with _ | (u | u) <;>
        rcases y with _ | (v | v) <;> simp only [mycielskian_adj] at hxy
      · exact ⟨v, fun w hw => hncyc (isCycle_mycielskianClosed_of_adj hw.symm)
          (by simp [Sym2.eq_swap, Walk.mycielskian]), rfl⟩
      · exact (hncyc (isCycle_mycielskianClosed_of_adj hxy)
          (by simp [Walk.mycielskian])).elim
      · exact (hncyc (isCycle_mycielskianClosed_of_adj hxy)
          (by simp [Walk.mycielskian])).elim
      · exact ⟨u, fun w hw => hncyc (isCycle_mycielskianClosed_of_adj hw.symm)
          (by simp [Sym2.eq_swap, Walk.mycielskian]), Sym2.eq_swap⟩
      · exact (hncyc (isCycle_mycielskianClosed_of_adj hxy.symm)
          (by simp [Sym2.eq_swap, Walk.mycielskian])).elim
  · rintro ⟨u, hiso, rfl⟩ h
    obtain ⟨_ | @⟨_, w, _, hadj, _⟩⟩ := h.symm
    rcases w with _ | (w | w) <;> simp_all [Sym2.eq_swap, IsIsolated]

/-!
# Trees

A graph is *acyclic* (a *forest*) if it contains no cycles. A *tree* is a connected
forest.

## Acyclic Graphs, Trees and Forests
-/
#source IsAcyclic

/-!
Acyclicity is downward monotone in the subgraph order (any subgraph of an acyclic
graph is acyclic), and induced subgraphs of forests are forests.
-/
#check SimpleGraph.IsAcyclic.anti
#check SimpleGraph.IsAcyclic.induce -- G.IsAcyclic → (G.induce s).IsAcyclic
/-!
`G.IsTree` says `G` is connected and acyclic, and each connected component of a
forest is a tree.
-/
#source SimpleGraph.IsTree
#check IsAcyclic.isTree_connectedComponent

/-!
A graph is acyclic iff every pair of vertices is connected by at most one path.
(Recall that `Subsingleton` means that a type has at most one element.)
-/
#check isAcyclic_iff_subsingleton_path
-- G.IsAcyclic ↔ ∀ (u v : V), Subsingleton (G.Path u v)

/-!
So a tree is a graph in which every pair of vertices is connected by a *unique*
path. In Mathlib this characterization needs `Nonempty V`: the graph on an empty
vertex type vacuously has unique paths, but it is not connected, so it is not a tree.
-/
#check isTree_iff_existsUnique_path

/-!
Trees are exactly the minimally connected graphs, and (again on a nonempty vertex
type) exactly the maximally acyclic graphs.
-/
#check isTree_iff_minimal_connected -- G.IsTree ↔ Minimal Connected G
#check isTree_iff_maximal_isAcyclic
/-!
Linking acyclicity and the cycle graphs: a graph is acyclic iff it does not contain
a copy of any cycle graph of order at least 3.
-/
#check isAcyclic_iff_free_cycleGraph

/-!
## The Infinite Path Is a Tree

Our running example `pathNat₁` is a tree. It is connected, since every vertex `n` can
be reached from `0` by walking up one step at a time.
-/
lemma pathNat₁_connected : pathNat₁.Connected := by
  refine (connected_iff_exists_forall_reachable _).2 ⟨0, fun n => ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (by simp : pathNat₁.Adj n (n + 1)).reachable

/-!
To see that `pathNat₁` is acyclic, consider the largest vertex `m` of a cycle. It has
two neighbours on the cycle (`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`), but
its only neighbour that is not larger than `m` is `m - 1`.
-/
lemma pathNat₁_isAcyclic : pathNat₁.IsAcyclic := by
  intro v c hc
  have hne : c.support.toFinset.Nonempty := ⟨v, by simp⟩
  -- let `m` be the largest vertex of the cycle `c`
  obtain ⟨m, hm_mem, hm_max⟩ := c.support.toFinset.exists_max_image id hne
  rw [List.mem_toFinset] at hm_mem
  -- `m` has exactly two neighbours in the cycle,
  --  considered as a subgraph of `pathNat₁`
  have hcard := hc.ncard_neighborSet_toSubgraph_eq_two hm_mem
  -- but its neighbours in the cycle are a subset of `{m - 1}`
  -- since `m` is the largest vertex
  have h_sub : c.toSubgraph.neighborSet m ⊆ ({m - 1} : Set ℕ) := by
    intro w hw
    rw [Subgraph.mem_neighborSet] at hw
    have hadj : pathNat₁.Adj m w := c.toSubgraph.adj_sub hw
    have hw_in : w ∈ c.support := Walk.mem_support_of_adj_toSubgraph hw.symm
    have hw_le : w ≤ m := hm_max w (List.mem_toFinset.mpr hw_in)
    grind
  have hle := Set.ncard_le_ncard h_sub (Set.finite_singleton _)
  rw [Set.ncard_singleton] at hle
  grind

lemma pathNat₁_isTree : pathNat₁.IsTree := ⟨pathNat₁_connected, pathNat₁_isAcyclic⟩

/-!
## The Edge Count Formula

A fundamental fact about finite trees: a tree on `n` vertices has exactly `n - 1`
edges. Mathlib states this as `#G.edgeFinset + 1 = Fintype.card V`, which avoids the
truncated subtraction of `ℕ`: working with `n - 1` would need the side condition
`1 ≤ n` at every step.
-/
#check IsTree.card_edgeFinset -- #G.edgeFinset + 1 = Fintype.card V
/-!
Conversely, a finite connected graph with this many edges is a tree.
-/
#check isTree_iff_connected_and_card
/-!
More generally, a connected graph satisfies `|V| ≤ |E(G)| + 1`. This is stated with
`Nat.card`, so it needs no finiteness assumption, but for an infinite graph it says
nothing: `Nat.card` of an infinite type is the junk value `0`, so for `pathNat₁` it
says `0 ≤ 0 + 1`.
-/
#check Connected.card_vert_le_card_edgeSet_add_one
/-!
Any nontrivial finite tree has at least two leaves (vertices of degree one), and so
its minimum degree is `1`. (Note `Nontrivial V` is the typeclass saying that `V`
contains at least two elements.)
-/
#check IsTree.exists_ne_and_degree_eq_one
#check IsTree.minDegree_eq_one_of_nontrivial
/-!
Deleting a leaf from a connected graph leaves it connected. This is the basic tool
for proving results about finite trees by induction on the number of vertices.
-/
#check Connected.induce_compl_singleton_of_degree_eq_one
/-!
## Trees and Bridges

A graph is acyclic if and only if every edge is a bridge. For example, every edge of
`pathNat₁` is a bridge.
-/
#check isAcyclic_iff_forall_adj_isBridge

example {m n : ℕ} (h : pathNat₁.Adj m n) : pathNat₁.IsBridge s(m, n) :=
  isAcyclic_iff_forall_adj_isBridge.mp pathNat₁_isAcyclic h

/-!
## Spanning Trees

A *spanning tree* of a connected graph `G` is a spanning subgraph that is a tree.
Every connected graph has a spanning tree. Since `T` and `G` are both of type
`SimpleGraph V`, the subgraph `T ≤ G` is automatically spanning (see
[Spanning Subgraphs](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-spanning-subgraphs)).

[Figure: A spanning tree in the Grötzsch graph](https://jt496.github.io/GraphTheoryInLean/figures/spanning_tree.svg)
-/
#check Connected.exists_isTree_le
/-!
Every graph `G` has a spanning forest (an acyclic spanning subgraph `F` in which any
pair of vertices is joined by a walk in `F` iff it is joined by a walk in `G`).
Notice that there is no finiteness condition here; the proof uses a maximality
argument via Zorn's lemma.
-/
#check exists_isAcyclic_reachable_eq_le

/-!
# Odd Cycles and Bipartite Graphs

Recall from
[Bipartite Graphs](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-bipartite-graphs)
that `G.IsBipartite` is defined as `G.Colorable 2`, and that forests are bipartite
(`IsAcyclic.colorable_two`): a forest has no cycles at all, let alone odd ones.
Mathlib contains the following result saying that a graph is bipartite iff every
closed walk has even length.
-/
#check two_colorable_iff_forall_loop_even
  -- G.Colorable 2 ↔ ∀ u (w : G.Walk u u), Even w.length
/-!
However we would like the stronger result about cycles rather than closed walks: a
graph is bipartite iff it contains no odd cycle. One direction is immediate, since a
cycle is a closed walk. For the other we need to show that a closed walk of odd
length contains a cycle of odd length. This is not currently in Mathlib (it is listed
as a TODO in Mathlib's file on bipartite graphs).

A key step is `Walk.cons_isCycle_iff_length_ne_one` from
[Circuits and Cycles](https://jt496.github.io/GraphTheoryInLean/Walks/#section-circuits-and-cycles):
a path closed up by an edge is a cycle, unless the path is just that edge.
-/
#check Walk.cons_isCycle_iff_length_ne_one

/-!
Next we show that any walk can be replaced by a path between the same endpoints whose
length has the same parity, unless the graph has an odd cycle. The proof is by
induction on the walk, in the style of Mathlib's `Walk.bypass`. Given a path `q`
from `c` to `b` (with the same parity as the original walk) and an edge `a — c`,
either `a` is not on `q` and `cons h q` is a path, or we split `q` at `a`. In the
second case, if the closed walk `cons h (q.takeUntil a)` has odd length then it is
an odd cycle; otherwise the rest of the path, `q.dropUntil a`, has the right parity.
-/
lemma Walk.exists_isPath_or_odd_isCycle {a b : V} (p : G.Walk a b) :
    (∃ q : G.Walk a b, q.IsPath ∧ (Even q.length ↔ Even p.length)) ∨
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  classical
  induction p with
  | nil => exact .inl ⟨nil, .nil, Iff.rfl⟩
  | @cons a _ _ h p ih =>
    rcases ih with ⟨q, hq, hpar⟩ | hodd
    · by_cases ha : a ∈ q.support
      · have hlen := congrArg length (q.take_spec ha)
        rw [length_append] at hlen
        rcases Nat.even_or_odd (q.takeUntil a ha).length with he | ho
        · exact .inr ⟨a, cons h (q.takeUntil a ha),
            (cons_isCycle_iff_length_ne_one _ h).mpr ⟨hq.takeUntil ha, by grind⟩,
            by grind [length_cons]⟩
        · exact .inl ⟨q.dropUntil a ha, hq.dropUntil ha, by grind [length_cons]⟩
      · exact .inl ⟨cons h q, hq.cons ha, by grind [length_cons]⟩
    · exact .inr hodd

/-!
Now an odd closed walk `cons h p` contains an odd cycle: either the previous lemma
finds one directly, or it replaces `p` by a path `q` of even length, and then
`cons h q` is an odd cycle.
-/
theorem Walk.exists_odd_isCycle {u : V} (w : G.Walk u u) (hw : Odd w.length) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  cases w with
  | nil => simp at hw
  | cons h p =>
    refine p.exists_isPath_or_odd_isCycle.elim (fun ⟨q, hq, hpar⟩ => ?_) id
    have hqe : Even q.length := by grind [length_cons]
    exact ⟨_, cons h q, (cons_isCycle_iff_length_ne_one _ h).mpr ⟨hq, by grind⟩,
      by grind [length_cons]⟩

/-!
Hence a graph is bipartite iff it has no odd cycle.
-/
theorem isBipartite_iff_forall_isCycle_even :
    G.IsBipartite ↔ ∀ u (c : G.Walk u u), c.IsCycle → Even c.length := by
  refine ⟨fun h u c _ => two_colorable_iff_forall_loop_even.mp h u c, fun h => ?_⟩
  refine two_colorable_iff_forall_loop_even.mpr fun u w => ?_
  by_contra hw
  obtain ⟨v, c, hc, hodd⟩ := w.exists_odd_isCycle (Nat.not_even_iff_odd.mp hw)
  exact Nat.not_even_iff_odd.mpr hodd (h v c hc)

/-!
## Cycles in Graphs of Maximum Degree Two

In a graph in which every vertex has degree at most `2`, a cycle passes through
every vertex of its connected component. Indeed, if some vertex reachable from the
cycle `c` lay off it, then some edge `y — z` of a walk to it would leave the cycle,
with `y ∈ c.support` and `z ∉ c.support` (`Walk.exists_boundary_dart`). But `y`
already has two neighbours on the cycle
(`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`), so together with `z` it would
have degree at least `3`.
-/
lemma Walk.IsCycle.mem_support_of_degree_le_two [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ 2) {u v : V} {c : G.Walk u u} (hc : c.IsCycle)
    (huv : G.Reachable u v) : v ∈ c.support := by
  by_contra hv
  obtain ⟨d, -, hd₁, hd₂⟩ :=
    huv.some.exists_boundary_dart {x | x ∈ c.support} c.start_mem_support hv
  have hsub : insert d.snd (c.toSubgraph.neighborSet d.fst) ⊆ G.neighborSet d.fst :=
    Set.insert_subset d.adj fun x hx => c.toSubgraph.adj_sub hx
  have hnot : d.snd ∉ c.toSubgraph.neighborSet d.fst := fun h =>
    hd₂ (c.mem_support_of_adj_toSubgraph h.symm)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hnot
      ((Set.toFinite _).subset ((Set.subset_insert _ _).trans hsub)),
    ncard_neighborSet_toSubgraph_eq_two hc hd₁, ncard_neighborSet] at this
  grind

/-!
In particular, every cycle in a connected graph of maximum degree at most `2` is a
*Hamiltonian cycle*
([Hamiltonian Paths and Cycles](https://jt496.github.io/GraphTheoryInLean/Walks/#section-hamiltonian-paths-and-cycles)):
the tail of a cycle is a path (`Walk.IsCycle.isPath_tail`), and a path through every
vertex is Hamiltonian (`Walk.IsPath.isHamiltonian_of_mem`).
-/
lemma Walk.IsCycle.isHamiltonianCycle_of_degree_le_two [DecidableEq V]
    [G.LocallyFinite] (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) : c.IsHamiltonianCycle :=
  ⟨hc, hc.isPath_tail.isHamiltonian_of_mem fun v => by
    rw [support_tail_of_not_nil _ hc.not_nil, mem_support_tail_iff hc.not_nil]
    exact hc.mem_support_of_degree_le_two hdeg (hconn u v)⟩

/-!
# Eulerian Circuits and Trails

Mathlib has the necessary conditions in Euler's theorem (see
[Eulerian Trails](https://jt496.github.io/GraphTheoryInLean/Walks/#section-eulerian-trails)),
but not the existence direction: a connected graph with all degrees even has an
Eulerian circuit, and a connected graph with exactly two vertices of odd degree has
an Eulerian trail. We prove these here with a splicing argument in the style of
*Hierholzer's algorithm*. Rather than running the algorithm, we take a longest trail
and show that, if it were not Eulerian, we could splice a circuit into it to make it
longer.

A standard proof might typically prove this for the all-even circuit case first and
then argue that the open trail case reduces to the closed circuit case by adding a
new vertex and two new edges from the odd degree vertices to the new vertex. This
would definitely be possible in Lean, but somehow more complicated than necessary.
Instead we prove the open case directly, reusing code from the circuit case.

[Figure: Hierholzer's splicing step on $K_5$: splice a new circuit $c$ (red) into the trail $p$ (blue) at vertex $w$ to obtain an Eulerian circuit](https://jt496.github.io/GraphTheoryInLean/figures/hierholzer.svg)
-/

section EulerExistence

/-!
Euler's theorem is often stated for connected graphs, but, as we saw in
[Eulerian Trails](https://jt496.github.io/GraphTheoryInLean/Walks/#section-eulerian-trails),
`IsEulerian` ignores isolated vertices. The analogous necessary condition is that all
the edges of `G` lie in a single connected component. We make this a definition
`EdgesInOneComponent`.
-/
/-- Every edge of `G` lies in a single connected component: any two non-isolated
vertices are reachable from each other. This is the weakest hypothesis under which
the Eulerian existence theorems below hold, strictly weaker than `Connected`,
which also forbids isolated vertices and the empty graph. -/
def EdgesInOneComponent (G : SimpleGraph V) : Prop :=
  ∀ u ∈ G.support, ∀ v ∈ G.support, G.Reachable u v

/-!
A connected graph has all its edges in one component (indeed all its vertices are
mutually reachable). This allows the Eulerian existence results to be stated for the
weaker `EdgesInOneComponent` and recovered for `Connected` as corollaries.
-/
lemma Connected.edgesInOneComponent (h : G.Connected) : G.EdgesInOneComponent :=
  fun u _ v _ => h u v

/-!
Conversely, `EdgesInOneComponent` is necessary: an Eulerian walk uses every edge, so
both endpoints of every edge lie on the walk, and all vertices of a walk are mutually
reachable.
-/
lemma Walk.IsEulerian.edgesInOneComponent [DecidableEq V] {u v} {p : G.Walk u v}
    (hp : p.IsEulerian) : G.EdgesInOneComponent := by
  have hmem : ∀ z ∈ G.support, z ∈ p.support := fun z hz =>
    hp.mem_support_of_not_isIsolated ((G.mem_support_iff_not_isIsolated).mp hz)
  exact fun x hx y hy =>
    ((p.takeUntil x (hmem x hx)).reachable).symm.trans
      (p.takeUntil y (hmem y hy)).reachable

/-!
Mathlib has the corresponding statement for `Connected`: if `G` has an Eulerian walk
and no isolated vertices, then `G` is connected.
-/
#check IsEulerian.connected_of_forall_not_isIsolated

/-!
As we saw in
[Eulerian Trails](https://jt496.github.io/GraphTheoryInLean/Walks/#section-eulerian-trails),
an Eulerian walk forces the edge set to be finite (`IsEulerian.fintypeEdgeSet`). So
for any `G` with `[Nonempty V]`, `G` has an Eulerian walk iff

* `G.edgeSet.Finite`,
* `G.EdgesInOneComponent`, and
* the set of vertices of odd degree has exactly 0 or 2 elements.

We prove the existence direction in this generality, assuming only
`[Finite G.edgeSet]`, so infinitely many isolated vertices are allowed. For the full
characterization we assume `[Finite V]`, as Mathlib's half of it does.

Our statements assume `[G.LocallyFinite]` rather than `[DecidableRel G.Adj]`, since
what they mention are degrees (see
[Instance Arguments in Statements](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-instance-arguments-in-statements)),
so they apply whichever instance a graph's neighbourhoods carry. The proofs also talk
about degrees in the graphs `G.deleteEdges s` obtained by deleting edges, so we first
give these graphs a `LocallyFinite` instance of their own.
-/
/-- Neighbourhoods in `G.deleteEdges s` are finite whenever those in `G` are. -/
@[instance_reducible]
def locallyFiniteDeleteEdges [G.LocallyFinite] [DecidableEq V] (s : Set (Sym2 V))
    [DecidablePred (· ∈ s)] : (G.deleteEdges s).LocallyFinite := fun v =>
  Fintype.ofFinset ((G.neighborFinset v).filter fun w => s(v, w) ∉ s) fun w => by
    simp
/-!
As with `locallyFiniteOfFintypeEdgeSet` in
[Finite Neighbourhoods](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-finite-neighbourhoods),
we make this a `def` rather than an `instance`. As a global instance it would create
a diamond: when `V` is a `Fintype` and `G.Adj` is decidable, Mathlib already gives
the neighbourhoods of `G.deleteEdges s` a `Fintype` instance, and ours would be a
second, different one.

Instead we use the `attribute` command, which attaches an attribute to a declaration
that already exists: `attribute [simp] foo` has the same effect as writing `@[simp]`
in front of the declaration of `foo`. The keyword `local` limits the effect to the
current `section` or `namespace`. So after the line below, typeclass inference uses
`locallyFiniteDeleteEdges` until `end EulerExistence`, and nowhere else.
-/
attribute [local instance] locallyFiniteDeleteEdges

/-!
## Extending Trails

In an all-even-degree graph, a trail that has not returned to its start can be
extended: its current endpoint `w ≠ v` is incident to an edge the trail has not used.
(The number of edges in the trail that are incident with `w` is odd, while `degree w`
is even, so some incident edge is still unused.)

We first prove a simple lemma about the number of edges of a trail `p` incident to a
vertex `x`. Since a trail does not repeat edges, the number of edges of `G` at `x`
used by a trail `p` is the number of entries of `p.edges` containing `x`.
-/
namespace Walk
open Finset
variable [G.LocallyFinite]

@[grind =>]
lemma IsTrail.card_filter_incidenceFinset [DecidableEq V] {u v} {p : G.Walk u v}
    (hp : p.IsTrail) (x : V) :
    #((G.incidenceFinset x).filter (· ∈ p.edges))
      = p.edges.countP (fun e => x ∈ e) := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
  congr 1; ext e
  simp only [mem_filter, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  grind [p.edges_subset_edgeSet]
/-!
So in an all-even-degree graph, a trail that has not returned to its start leaves
some edge at its endpoint unused.
-/
lemma IsTrail.exists_unused_edge_of_even {v w} (h2 : ∀ x, Even (G.degree x))
    {p : G.Walk v w} (hp : p.IsTrail) (hvw : v ≠ w) :
    ∃ x, G.Adj w x ∧ s(w, x) ∉ p.edges := by
  classical
  -- the number of edges in `p` that are incident to `w` is odd
  have hodd : ¬ Even (p.edges.countP (fun e => w ∈ e)) := by
    rw [hp.even_countP_edges_iff w]; simp [hvw]
  -- if every edge at `w` were used, that number would be `degree w`, which is even
  by_contra! h
  apply hodd
  rw [← hp.card_filter_incidenceFinset, filter_true_of_mem,
    card_incidenceFinset_eq_degree]
  · exact h2 w
  · intro e he
    rw [mem_incidenceFinset] at he
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp he.2
    exact h x he.1

/-!
A trail repeats no edges, so its length is at most the number of edges in the graph.
-/
#check IsTrail.length_le_card_edgeFinset  -- p.IsTrail → p.length ≤ #G.edgeFinset

/-!
In an all-even-degree graph, any trail `p` starting at `v` can be extended to a
closed trail from `v` of length at least `p.length`, by repeatedly applying
`exists_unused_edge_of_even` until it returns to `v`.

Note this proof applies `exists_closed_isTrail_length_le` recursively to longer
trails. It isn't obvious to Lean that this is well-founded so we need to give a
termination argument.

We know that no trail is longer than the number of edges in the graph:
`IsTrail.length_le_card_edgeFinset` and the trail we apply it to in the recursive
call is strictly longer than the original trail `p`, so the measure
`Nat.card G.edgeSet - p.length` strictly decreases with each recursive call. (This is
what we are doing in the `termination_by` and `decreasing_by` section below.) The
lemma assumes `[Finite G.edgeSet]`: in a graph with infinitely many edges, such as
the two-way infinite path, a trail can be extended forever.
-/
lemma IsTrail.exists_closed_isTrail_length_le [Finite G.edgeSet]
    (h2 : ∀ x, Even (G.degree x)) {v w} {p : G.Walk v w} (hp : p.IsTrail) :
    ∃ q : G.Walk v v, q.IsTrail ∧ p.length ≤ q.length := by
  -- if `v = w` then `p` is already a closed trail so we are done
  by_cases hvw : v = w
  · subst hvw; exact ⟨p, hp, le_refl _⟩
  · -- we get an edge from the end of `p` that is not used by `p`
    obtain ⟨x, hadj, hnotin⟩ := hp.exists_unused_edge_of_even h2 hvw
    -- concatenating this edge to `p` gives a longer trail
    have hp' : (p.concat hadj).IsTrail := hp.concat hadj hnotin
    -- Call the theorem recursively on this longer trail.
    obtain ⟨q, hq, hlen⟩ := hp'.exists_closed_isTrail_length_le h2
    exact ⟨q, hq, by grind [length_concat]⟩
termination_by Nat.card G.edgeSet - p.length
decreasing_by
  have : Fintype G.edgeSet := (Set.toFinite _).fintype
  have he : (p.concat hadj).length = p.length + 1 := length_concat ..
  have hb : (p.concat hadj).length ≤ Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
    exact hp'.length_le_card_edgeFinset
  grind

/-!
Starting from any vertex of positive degree in an all-even-degree graph there is a
circuit (a nonempty closed trail).
-/
lemma _root_.SimpleGraph.exists_isCircuit_of_even [Finite G.edgeSet] {v}
    (hv : 0 < G.degree v) (h2 : ∀ x, Even (G.degree x)) :
    ∃ p : G.Walk v v, p.IsCircuit := by
  obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  obtain ⟨q, hq, hlen⟩ := hu.isPath_toWalk.isTrail.exists_closed_isTrail_length_le h2
  exact ⟨q, hq, by rintro rfl; simp at hlen⟩

variable [DecidableEq V]
/-!
Deleting the edges of a trail `p` changes the degree at each vertex `x` by the number
of edges of `p` incident to `x`. Hence if this number has the same parity as
`G.degree x` at every vertex, then every degree in the deleted graph is even.
-/
lemma IsTrail.even_degree_deleteEdges {u v} {p : G.Walk u v} (hp : p.IsTrail)
    (hpar : ∀ x, Even (p.edges.countP (fun e => x ∈ e)) ↔ Even (G.degree x)) :
    ∀ x, Even ((G.deleteEdges {e | e ∈ p.edges}).degree x) := by
  intro x
  have hinc : (G.deleteEdges {e | e ∈ p.edges}).incidenceFinset x
            = (G.incidenceFinset x).filter (· ∉ p.edges) := by
    ext e
    simp only [mem_filter, mem_incidenceFinset, incidenceSet, edgeSet_deleteEdges,
      Set.mem_ofPred_eq, Set.mem_sdiff]
    grind
  -- the deleted degree at `x` plus the number of edges of
  -- `p` at `x` is the original degree
  grind [card_filter_add_card_filter_not, card_incidenceFinset_eq_degree]

/-!
So in an all-even-degree graph, deleting the edges of a closed trail preserves the
property that every degree is even (a closed trail uses an even number of edges at
every vertex).
-/
lemma IsTrail.even_degree_deleteEdges_closed {v} {p : G.Walk v v} (hp : p.IsTrail)
    (h2 : ∀ x, Even (G.degree x)) :
    ∀ x, Even ((G.deleteEdges {e | e ∈ p.edges}).degree x) :=
  hp.even_degree_deleteEdges fun x => by rw [hp.even_countP_edges_iff x]; simp [h2 x]

/-!
Deleting the edges of an open trail from `a` to `b` flips the degree parity at
exactly its two endpoints. So if `a` and `b` are the only vertices of odd degree,
then every degree in the deleted graph is even.
-/
lemma IsTrail.even_degree_deleteEdges_open {a b} (hab : a ≠ b) {p : G.Walk a b}
    (hp : p.IsTrail) (hpar : ∀ x, Even (G.degree x) ↔ x ≠ a ∧ x ≠ b) :
    ∀ x, Even ((G.deleteEdges {e | e ∈ p.edges}).degree x) :=
  hp.even_degree_deleteEdges fun x =>
    by rw [hp.even_countP_edges_iff x, hpar x]; simp [hab]

/-!
Let `p : G.Walk u v` be a trail in a graph `G` whose edges all lie in one component.
If `u` is not an isolated vertex and `p` is not Eulerian, then some vertex of `p`
still has positive degree in the graph obtained by deleting the edges of `p`.
-/
lemma IsTrail.exists_support_pos_deleted {u v} (hG : G.EdgesInOneComponent)
    (hu : u ∈ G.support) {p : G.Walk u v}
    (hp : p.IsTrail) (hne : ¬ p.IsEulerian) :
    ∃ w ∈ p.support, 0 < (G.deleteEdges {e | e ∈ p.edges}).degree w := by
  let Gp := G.deleteEdges {e | e ∈ p.edges}
  -- some edge `a — b` of `G` is not used by `p`
  obtain ⟨e, he, hep⟩ : ∃ e ∈ G.edgeSet, e ∉ p.edges := by
    by_contra! h; exact hne (hp.isEulerian_of_forall_mem h)
  induction e using Sym2.ind with | _ a b => ?_
  have hab : G.Adj a b := he
  have hGab : Gp.Adj a b := by rw [deleteEdges_adj]; exact ⟨hab, hep⟩
  have hpos : ∀ {x y}, Gp.Adj x y → 0 < Gp.degree x :=
    fun {x y} hxy => (Gp.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
  by_cases ha : a ∈ p.support
  · exact ⟨a, ha, hpos hGab⟩
  · obtain ⟨q⟩ := hG a hab.left_mem_support u hu
    obtain ⟨⟨⟨c, d⟩, hcd⟩, -, ⟨hc, hd⟩⟩ :=
      q.reverse.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support ha
    have hcd_notin : s(c, d) ∉ p.edges :=
      fun hmem => hd (p.snd_mem_support_of_mem_edges hmem)
    have hcdGp : Gp.Adj c d := by rw [deleteEdges_adj]; exact ⟨hcd, hcd_notin⟩
    exact ⟨c, hc, hpos hcdGp⟩

variable [Finite G.edgeSet]
/-!
A non-Eulerian trail `p` from `a` to `b` can be extended, provided every vertex has
even degree in the graph obtained by deleting the edges of `p`. Find a vertex `w` on
`p` incident to an unused edge, build a circuit `c` at `w` in the
deleted graph, transfer it back into `G`, and splice it into `p` at `w`.

We splice `c` in place by splitting `p` as `(p.takeUntil w) ++ (p.dropUntil w)`
and inserting `c` to get `(p.takeUntil w) ++ c ++ (p.dropUntil w)`.

[Figure](https://jt496.github.io/GraphTheoryInLean/figures/euler_two_odd.svg)

Notice that this lemma will allow us to handle both the closed case (`a = b`, the
Eulerian *circuit*, where the parity hypothesis `hdel` comes from
`even_degree_deleteEdges_closed`) and the open case (`a ≠ b`, the Eulerian *trail*,
where it comes from `even_degree_deleteEdges_open`).
-/
lemma IsTrail.exists_longer_of_not_isEulerian {a b} (hG : G.EdgesInOneComponent)
    (ha : a ∈ G.support) {p : G.Walk a b}
    (hp : p.IsTrail) (hdel : ∀ x, Even ((G.deleteEdges {e | e ∈ p.edges}).degree x))
    (hne : ¬ p.IsEulerian) :
    ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by
  -- some vertex `w` on `p` is incident to an edge of `G` unused by `p`
  obtain ⟨w, hw_supp, hw_pos⟩ := hp.exists_support_pos_deleted hG ha hne
  -- build a circuit `c` at `w` in the deleted graph, which has fewer edges than `G`
  have : Finite (G.deleteEdges {e | e ∈ p.edges}).edgeSet :=
    Finite.Set.subset _ (edgeSet_mono (deleteEdges_le _))
  obtain ⟨c, hc⟩ := exists_isCircuit_of_even hw_pos hdel
  -- every edge of `c` is an edge of `G`, so `c` transfers back into `G`
  have htr : ∀ e ∈ c.edges, e ∈ G.edgeSet := fun e he =>
    edgeSet_mono (deleteEdges_le _) (c.edges_subset_edgeSet he)
  -- the edges of the transferred `c` are unused by `p`
  have hc_notin : ∀ e ∈ (c.transfer G htr).edges, e ∉ p.edges := by
    intro e he hpe
    rw [edges_transfer] at he
    have heg := c.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at heg
    exact heg.2 hpe
  -- splice `c` into `p` at `w`: walk `a → w`, then around `c`, then `w → b`
  let spl := (p.takeUntil w hw_supp).append
                ((c.transfer G htr).append (p.dropUntil w hw_supp))
  have hspl_trail : spl.IsTrail := by
    simp only [spl, isTrail_append, edges_append]
    refine ⟨hp.takeUntil hw_supp,
              ⟨hc.isTrail.transfer htr, hp.dropUntil hw_supp, ?_⟩, ?_⟩
    · -- the edges of `c` are disjoint from the `w → b` part of `p`
      exact fun e he hf => hc_notin e he (edges_dropUntil_subset_edges p hw_supp hf)
    · -- the `a → w` part of `p` is disjoint from both `c` and the `w → b` part
      intro e het he'
      rcases List.mem_append.mp he' with hec | hed
      · exact hc_notin e hec (edges_takeUntil_subset_edges p hw_supp het)
      · exact hp.disjoint_edges_takeUntil_dropUntil hw_supp het hed
  -- the spliced walk is a strictly longer trail from `a` to `b`
  refine ⟨spl, hspl_trail, ?_⟩
  have hsp := congrArg Walk.length (p.take_spec hw_supp)
  rw [length_append] at hsp
  grind [length_append, length_transfer, hc.three_le_length]

/-!
## Euler's Theorem

Both cases of Euler's theorem follow the same pattern. Let `q` be a longest trail
from `a` to `b` (trails have length at most `#G.edgeFinset`, so one exists as soon
as there is any trail `q₀` from `a` to `b`). If `q` were not Eulerian then
`IsTrail.exists_longer_of_not_isEulerian` would give a longer trail, a
contradiction. The two cases differ only in why deleting the edges of a trail leaves
every degree even, so we take this as the hypothesis `hdel`.
-/
lemma exists_isEulerian_of_isTrail {a b} (hG : G.EdgesInOneComponent)
    (ha : a ∈ G.support) {q₀ : G.Walk a b} (hq₀ : q₀.IsTrail)
    (hdel : ∀ q : G.Walk a b, q.IsTrail →
      ∀ x, Even ((G.deleteEdges {e | e ∈ q.edges}).degree x)) :
    ∃ p : G.Walk a b, p.IsEulerian := by
  classical
  have : Fintype G.edgeSet := (Set.toFinite _).fintype
  -- `P k` says there is a trail from `a` to `b` of length `k`
  let P : ℕ → Prop := fun k => ∃ q : G.Walk a b, q.IsTrail ∧ q.length = k
  -- let `q` be a longest trail from `a` to `b`
  obtain ⟨q, hq, hq_len⟩ := Nat.findGreatest_spec (P := P) (m := q₀.length)
    (n := #G.edgeFinset) hq₀.length_le_card_edgeFinset ⟨q₀, hq₀, rfl⟩
  refine ⟨q, by_contra fun hne => ?_⟩
  -- the graph with `q`'s edges deleted has even degrees, so `q` can be extended
  obtain ⟨q', hq', hlt⟩ := hq.exists_longer_of_not_isEulerian hG ha (hdel q hq) hne
  have : q'.length ≤ Nat.findGreatest P #G.edgeFinset :=
    Nat.le_findGreatest hq'.length_le_card_edgeFinset ⟨q', hq', rfl⟩
  grind

/-!
*Euler's theorem* (existence direction): a graph with finitely many edges, all in one
component (`EdgesInOneComponent`), in which every vertex has even degree has an
Eulerian circuit. `[Nonempty V]` is needed only so that we can name a start vertex in
the edgeless case.
-/
theorem exists_isEulerian_circuit [Nonempty V] (h : G.EdgesInOneComponent)
    (h2 : ∀ v, Even (G.degree v)) :
    ∃ u : V, ∃ (p : G.Walk u u), p.IsEulerian := by
  by_cases hsupp : G.support.Nonempty
  · -- pick a non-isolated start `u`; a longest closed trail from `u` is Eulerian
    obtain ⟨u, hu⟩ := hsupp
    exact ⟨u, exists_isEulerian_of_isTrail h hu .nil
      fun q hq => hq.even_degree_deleteEdges_closed h2⟩
  · -- no non-isolated vertex: `G` is edgeless, so `nil` is Eulerian
    obtain ⟨u⟩ := ‹Nonempty V›
    exact ⟨u, nil,
      (isEulerian_nil_iff u).mpr (Set.not_nonempty_iff_eq_empty.mp hsupp)⟩

/-!
*Euler's theorem* (existence direction) for a **connected** graph: recovered from
`exists_isEulerian_circuit` via `Connected.edgesInOneComponent`.
-/
theorem _root_.SimpleGraph.Connected.exists_isEulerian_circuit (h : G.Connected)
    (h2 : ∀ v, Even (G.degree v)) :
    ∃ u : V, ∃ (p : G.Walk u u), p.IsEulerian :=
  have : Nonempty V := h.nonempty
  Walk.exists_isEulerian_circuit h.edgesInOneComponent h2

/-!
*Euler's theorem* (existence direction, open trail): if `G` has all edges in one
component (`EdgesInOneComponent`) and `a ≠ b` are the only two odd-degree vertices,
then `G` has an Eulerian trail from `a` to `b`.
-/
theorem exists_isEulerian_trail_of_two_odd {a b} (hG : G.EdgesInOneComponent)
    (hab : a ≠ b) (hpar : ∀ x, Even (G.degree x) ↔ x ≠ a ∧ x ≠ b) :
    ∃ p : G.Walk a b, p.IsEulerian := by
  -- the two odd-degree vertices `a`, `b` are non-isolated, hence in `G.support`
  have hsupp : a ∈ G.support ∧ b ∈ G.support := by
    simp only [← degree_pos_iff_mem_support]; grind [Odd.pos]
  -- since `a` and `b` lie in the same component there is a path, hence a trail
  obtain ⟨q₀, hq₀⟩ := (hG a hsupp.1 b hsupp.2).some.toPath
  exact exists_isEulerian_of_isTrail hG hsupp.1 hq₀.isTrail
    fun q hq => hq.even_degree_deleteEdges_open hab hpar

/-!
*Euler's theorem* (existence direction, open trail) for a **connected** graph:
recovered from `exists_isEulerian_trail_of_two_odd` via
`Connected.edgesInOneComponent`.
-/
theorem _root_.SimpleGraph.Connected.exists_isEulerian_trail {a b} (h : G.Connected)
    (hab : a ≠ b) (hpar : ∀ x, Even (G.degree x) ↔ x ≠ a ∧ x ≠ b) :
    ∃ p : G.Walk a b, p.IsEulerian :=
  exists_isEulerian_trail_of_two_odd h.edgesInOneComponent hab hpar

/-!
*Euler's theorem*, full characterization: a finite graph with at least one vertex has
an Eulerian trail **iff** all its edges lie in one component and it has either no
odd-degree vertex or exactly two. The forward direction is
`IsEulerian.edgesInOneComponent` with Mathlib's `IsEulerian.card_odd_degree`; the
reverse direction is `exists_isEulerian_circuit` (no odd-degree vertex) or
`exists_isEulerian_trail_of_two_odd` (exactly two). We only reason about the number
of odd-degree vertices, so we count them with `Set.ncard` (see
[Which One Should I Use?](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-which-one-should-i-use))
and `[Finite V]` suffices; it implies the section's `[Finite G.edgeSet]` assumption,
which we `omit`. Mathlib's `IsEulerian.card_odd_degree` counts with `Fintype.card`
instead, so the forward direction converts between the two.
-/
omit [Finite G.edgeSet] in
theorem exists_isEulerian_iff [Finite V] [Nonempty V] :
    (∃ u v, ∃ p : G.Walk u v, p.IsEulerian) ↔
      G.EdgesInOneComponent ∧ ({v | Odd (G.degree v)}.ncard = 0
        ∨ {v | Odd (G.degree v)}.ncard = 2) := by
  have := Fintype.ofFinite V
  refine ⟨fun ⟨_, _, _, hp⟩ => ⟨hp.edgesInOneComponent, by
    classical
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    convert hp.card_odd_degree⟩, ?_⟩
  rintro ⟨hG, h0 | h2⟩
  · -- no odd-degree vertex: every degree is even, so there is an Eulerian circuit
    rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem] at h0
    obtain ⟨u, p, hp⟩ := exists_isEulerian_circuit hG fun x =>
      Nat.not_odd_iff_even.mp (h0 x)
    exact ⟨u, u, p, hp⟩
  · -- exactly two odd-degree vertices `a, b`: an Eulerian trail from `a` to `b`
    rw [Set.ncard_eq_two] at h2
    obtain ⟨a, b, hab, hS⟩ := h2
    have hpar (x) : Even (G.degree x) ↔ x ≠ a ∧ x ≠ b := by
      simpa [← Nat.not_odd_iff_even] using (Set.ext_iff.mp hS x).not
    exact ⟨a, b, exists_isEulerian_trail_of_two_odd hG hab hpar⟩

end Walk
end EulerExistence

/-!
# Edge and Vertex Connectivity

Informally, a graph is `k`-edge-connected if deleting less than `k` edges always
leaves it connected, and `k`-vertex-connected if deleting less than `k` vertices
always leaves it connected. Mathlib has the first notion, and we define the second.

These are the *deletion* forms of the definitions. *Menger's theorem* gives the
equivalent *path* forms: a graph is `k`-edge-connected iff any two distinct vertices
are joined by `k` edge-disjoint paths, and a graph with more than `k` vertices is
`k`-vertex-connected iff any two distinct vertices are joined by `k` paths that share
only their endpoints. Menger's theorem is not currently in Mathlib.

## Edge Connectivity

In Mathlib edge connectivity is defined via `G.IsEdgeReachable`, which says that two
vertices `u v : V` are `k`-edge-reachable if after deleting less than `k` edges from
`G` there is still a walk from `u` to `v`. Here the number of deleted edges is
measured with `Set.encard`, which is `⊤` if the set is infinite and otherwise its
cardinality as a natural number.
-/
#check Set.encard

#source IsEdgeReachable

/-!
Notice that the set `s` of deleted edges is an arbitrary `Set (Sym2 V)`, so it may
contain pairs that are not edges of `G`. Deleting these does nothing, so this is
harmless, but it means that we sometimes have to filter them out (as in the proof of
`IsVertexConnected.isEdgeConnected` below).

A graph is `k`-edge-connected if every pair of vertices is `k`-edge-reachable.
-/
#source IsEdgeConnected

/-!
Beware that this only gives *pre*connectedness. If `G` is `k`-edge-connected for
`k ≠ 0` then it is preconnected, but a graph with at most one vertex (including the
graph with no vertices) is `k`-edge-connected for every `k`.
-/
#check IsEdgeConnected.preconnected

/-!
[Figure: A 3-edge-connected graph with a 3-edge cut](https://jt496.github.io/GraphTheoryInLean/figures/edge_connectivity.svg)

An edge is a bridge iff its endpoints are not 2-edge-reachable. So a graph is
2-edge-connected iff deleting any single edge leaves it preconnected, and a graph is
a forest iff no two distinct vertices are 2-edge-reachable.
-/
#check isBridge_iff_not_isEdgeReachable_two
#check isEdgeConnected_two
#check isAcyclic_iff_pairwise_not_isEdgeReachable_two

/-!
We will show later in this section that the hypercube `Q[n]` is
`n`-edge-connected, by deriving this from the fact that it is `n`-vertex-connected.

## Vertex Connectivity

A graph is `k`-vertex-connected if deleting less than `k` vertices always leaves the
graph connected. This isn't currently in Mathlib so we give a definition below. As is
standard, when we say *`k`-connected* without qualification we mean
`k`-vertex-connected.

Since graphs with no vertices are not connected we insist that the vertex type has
more than `k` vertices. We count the vertices with `ENat.card V` and, as for edge
connectivity, measure sets of vertices with the `ℕ∞`-valued `encard`, so that
infinite vertex types are handled correctly.

Rather than giving a definition in terms of the graph formed by deleting vertices,
we ask that for any set `S` of less than `k` vertices, and any pair of vertices not
in `S`, there is a walk in `G` between the pair which avoids `S`.
-/
/-- A graph is `k`-vertex-connected if deleting less than `k` vertices always leaves
the graph connected. -/
def IsVertexConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  (k + 1 : ℕ∞) ≤ ENat.card V ∧
    ∀ (S : Set V), S.encard < k → ∀ (u v : V), u ∉ S → v ∉ S →
      ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ S

/-!
The graph obtained by deleting `S` is `G.induce Sᶜ`, but its vertex type is the
subtype `↥Sᶜ`, so its walks run between vertices `⟨u, hu⟩` that carry proofs that
`u ∉ S`. Walks in `G` that avoid `S` are much easier to construct and combine.

The two formulations agree. To see this we pass through Mathlib's `Subgraph` API
([Induced Subgraphs](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-induced-subgraphs)):
`preconnected_induce_iff` turns preconnectedness of `G.induce Sᶜ` into
preconnectedness of the subgraph `(⊤ : G.Subgraph).induce Sᶜ`, and
`Subgraph.preconnected_iff_forall_exists_walk_subgraph` characterizes the latter by
walks `p` in `G` with `p.toSubgraph ≤ (⊤ : G.Subgraph).induce Sᶜ`. For an induced
subgraph this just says that every vertex of `p` lies in `Sᶜ`.
-/
lemma Walk.toSubgraph_le_induce_top_iff {W : Set V} {u v : V} (p : G.Walk u v) :
    p.toSubgraph ≤ (⊤ : G.Subgraph).induce W ↔ ∀ y ∈ p.support, y ∈ W := by
  refine ⟨fun h y hy => h.1 (p.mem_verts_toSubgraph.mpr hy), fun h => ?_⟩
  exact p.toSubgraph_le_induce_support.trans
    (Subgraph.induce_mono_right fun y hy => h y hy)

lemma isVertexConnected_iff_induce {k : ℕ} : G.IsVertexConnected k ↔
    (k + 1 : ℕ∞) ≤ ENat.card V ∧
      ∀ S : Set V, S.encard < k → (G.induce Sᶜ).Preconnected := by
  refine and_congr_right fun _ => forall₂_congr fun S _ => ?_
  rw [preconnected_induce_iff, Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  simp only [Subgraph.induce_verts, Set.mem_compl_iff,
    Walk.toSubgraph_le_induce_top_iff]

/-!
A set with less than `k` elements is finite, so it is enough to check the condition
for finsets, and conversely we can apply it to finsets.
-/
lemma IsVertexConnected.of_finset {k : ℕ}
    (hcard : (k + 1 : ℕ∞) ≤ ENat.card V)
    (h : ∀ (S : Finset V), S.card < k → ∀ (u v : V), u ∉ S → v ∉ S →
      ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ S) : G.IsVertexConnected k := by
  refine ⟨hcard, fun S hS u v hu hv => ?_⟩
  lift S to Finset V using
    Set.encard_lt_top_iff.mp (hS.trans (ENat.natCast_lt_top k))
  exact h S (by simpa using hS) u v hu hv

lemma IsVertexConnected.exists_walk {k : ℕ} (hG : G.IsVertexConnected k)
    (S : Finset V) (hS : S.card < k) (u v : V) (hu : u ∉ S) (hv : v ∉ S) :
    ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ S :=
  hG.2 S (by simpa using hS) u v hu hv

/-!
A `k`-vertex-connected graph has more than `k` vertices, so any finite set of at most
`k` vertices misses some vertex.
-/
lemma IsVertexConnected.exists_notMem {k : ℕ} (hG : G.IsVertexConnected k)
    (A : Finset V) (hA : A.card ≤ k) : ∃ x, x ∉ A := by
  refine A.exists_not_mem_of_card_lt_enatCard
    (lt_of_lt_of_le ?_ hG.1)
  exact_mod_cast Nat.lt_succ_of_le hA

/-!
If a graph is `k`-vertex-connected then any vertex has at least `k` neighbours: if
there were less than `k` neighbours `N` of `v`, then a walk from `v` to a vertex
outside `N ∪ {v}` avoiding `N` would have nowhere to take its first step. We state
this with `encard`, so that no finiteness assumption on the neighbourhood is needed.
-/
lemma IsVertexConnected.le_encard_neighborSet {k : ℕ} (hG : G.IsVertexConnected k)
    (v : V) : (k : ℕ∞) ≤ (G.neighborSet v).encard := by
  by_contra! hlt
  obtain ⟨u, hu⟩ : ∃ u, u ∉ insert v (G.neighborSet v) := by
    by_contra! h
    have := (hG.1.trans_eq (Set.encard_univ V).symm).trans
      ((Set.encard_le_encard fun x _ => h x).trans
      ((Set.encard_insert_le _ _).trans (Order.add_one_le_of_lt hlt)))
    norm_cast at this; grind
  rw [Set.mem_insert_iff, not_or] at hu
  obtain ⟨p, hp⟩ := hG.2 _ hlt v u (G.irrefl) hu.2
  cases p with
  | nil => exact hu.1 rfl
  | @cons _ w _ hadj p' => exact hp w (by simp) hadj

lemma IsVertexConnected.le_degree {k : ℕ} (hG : G.IsVertexConnected k) (v : V)
    [Fintype (G.neighborSet v)] : k ≤ G.degree v := by
  have h := hG.le_encard_neighborSet v
  rwa [← coe_neighborFinset, Set.encard_coe_eq_coe_finsetCard,
    card_neighborFinset_eq_degree, Nat.cast_le] at h

/-!
Taking the box product `G □ K₂` raises the vertex connectivity by at least one, so
`Q[n]` is `n`-vertex-connected by induction on `n`.

Proof sketch for the box-product step: Let `S` be a set of at most `k` vertices of
`G □ K₂` and let `(u, c)` and `(v, d)` be two vertices not in `S`. Write
`S.fiberProj b` for the set of vertices `z` of `G` with `(z, b) ∈ S`. The sizes of
`S.fiberProj true` and `S.fiberProj false` sum to `|S| ≤ k`, so for some fibre `b`
less than `k` vertices of `S` lie in that fibre (`Finset.exists_fiberProj_card_lt`).
We first walk from each endpoint into fibre `b` avoiding `S`
(`walk_to_fiber_avoids`): either the endpoint is already there, or its copy in fibre
`b` is not in `S` and we cross directly, or that copy lies in `S`, in which case some
`G`-neighbour `w` has both of its copies outside `S` (`exists_good_neighbor`), and we
step to `w` and cross there. Finally `k`-vertex-connectivity of `G` gives a walk in
`G` between the two projected endpoints avoiding `S.fiberProj b`, and this lifts to a
walk in fibre `b` avoiding `S` (`Walk.boxProdLeft`).
-/

/-- The vertices `z` of `G` whose copy `(z, b)` in fibre `b` of `G □ K₂` lies in
`S`. -/
noncomputable def _root_.Finset.fiberProj (S : Finset (V × Bool)) (b : Bool) :
    Finset V :=
  S.preimage (·, b) (Prod.mk_left_injective b).injOn

@[simp] lemma _root_.Finset.mem_fiberProj {S : Finset (V × Bool)} {b : Bool}
    {z : V} :
    z ∈ S.fiberProj b ↔ (z, b) ∈ S := Finset.mem_preimage

/-!
If `0 < k` and `|S| ≤ k` then some fibre contains less than `k` vertices of `S`.
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
If `(z, b) ∈ S` and `|S| ≤ k` then some `G`-neighbour `w` of `z` has neither copy
`(w, false)`, `(w, true)` in `S`: `z` has at least `k` neighbours, but at most
`k - 1` first coordinates of `S` differ from `z`.
-/
private lemma exists_good_neighbor {k : ℕ} (hG : G.IsVertexConnected k)
    {S : Finset (V × Bool)} (hS : S.card ≤ k) {z : V} {b : Bool} (hzb : (z, b) ∈ S) :
    ∃ w, G.Adj z w ∧ ∀ c, (w, c) ∉ S := by
  classical
  by_contra! h
  have hz : z ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hzb
  have hsub : G.neighborSet z ⊆ ↑((S.image Prod.fst).erase z) := fun w hw => by
    obtain ⟨c, hc⟩ := h w hw
    exact Finset.mem_erase.mpr ⟨hw.ne', Finset.mem_image_of_mem Prod.fst hc⟩
  have hk := (hG.le_encard_neighborSet z).trans (Set.encard_le_encard hsub)
  grind [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le, Finset.card_erase_of_mem hz]

/-!
From a vertex `(z, c) ∉ S` there is a walk of length at most two into fibre `b`
that avoids `S`.
-/
private lemma walk_to_fiber_avoids {k : ℕ} (hG : G.IsVertexConnected k)
    {S : Finset (V × Bool)} (hS : S.card ≤ k) {z : V} {c : Bool} (hzc : (z, c) ∉ S)
    (b : Bool) :
    ∃ (z' : V) (p : (G.boxProd (⊤ : SimpleGraph Bool)).Walk (z, c) (z', b)),
      ∀ x ∈ p.support, x ∉ S := by
  by_cases hcb : c = b
  · subst hcb
    exact ⟨z, .nil, by simp [hzc]⟩
  have hcross (w : V) : (G.boxProd ⊤).Adj (w, c) (w, b) := boxProd_adj_right.mpr hcb
  by_cases hzb : (z, b) ∈ S
  · obtain ⟨w, hzw, hw⟩ := exists_good_neighbor hG hS hzb
    exact ⟨w, .cons (boxProd_adj_left.mpr hzw) (hcross w).toWalk, by simp [hzc, hw]⟩
  · exact ⟨z, (hcross z).toWalk, by simp [hzc, hzb]⟩

/-!
Mathlib's `Walk.boxProdLeft` copies a walk of `G` into fibre `b` of `G □ H`. It
is defined as a `Walk.map`, but its type records the endpoints as `(u, b)` and
`(v, b)`, whereas the endpoints of the `Walk.map` walk only reduce to these after
unfolding `boxProdLeft`.
-/
@[simp] lemma Walk.support_boxProdLeft {β : Type*} (H : SimpleGraph β) (b : β)
    {u v : V} (p : G.Walk u v) :
    (p.boxProdLeft H b).support = p.support.map (·, b) :=
  Walk.support_map _ _

/-!
If `G` is `k`-vertex-connected then `G □ K₂` is `(k + 1)`-vertex-connected.
-/
lemma IsVertexConnected.boxProd_top_bool {k : ℕ} (hG : G.IsVertexConnected k)
    (hG_conn : G.Connected) :
    (G.boxProd (⊤ : SimpleGraph Bool)).IsVertexConnected (k + 1) := by
  refine .of_finset ?_ ?_
  · -- `|V × Bool| = 2 |V|` and `k + 1 ≤ |V|`
    have h := hG.1
    rw [ENat.card_prod, ENat.card_eq_coe_fintype_card (α := Bool), Fintype.card_bool,
      Nat.cast_ofNat]
    calc ((k + 1 : ℕ) : ℕ∞) + 1 ≤ ((k : ℕ∞) + 1) * 2 := by norm_cast; grind
      _ ≤ _ := by gcongr
  intro S hS ⟨u, c⟩ ⟨v, d⟩ hu hv
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- for `k = 0` the set `S` is empty and `G □ K₂` is connected
    obtain ⟨p⟩ := (hG_conn.boxProd connected_top).preconnected (u, c) (v, d)
    exact ⟨p, by simp [Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hS)]⟩
  have hS' : S.card ≤ k := Nat.le_of_lt_succ hS
  obtain ⟨b, hb⟩ := S.exists_fiberProj_card_lt hS' hk
  obtain ⟨u', pu, hpu⟩ := walk_to_fiber_avoids hG hS' hu b
  obtain ⟨v', pv, hpv⟩ := walk_to_fiber_avoids hG hS' hv b
  obtain ⟨q, hq⟩ := hG.exists_walk (S.fiberProj b) hb u' v'
    (by simpa using hpu _ pu.end_mem_support)
    (by simpa using hpv _ pv.end_mem_support)
  refine ⟨pu.append ((q.boxProdLeft ⊤ b).append pv.reverse), fun x hx => ?_⟩
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse,
    Walk.support_boxProdLeft, List.mem_map] at hx
  grind [Finset.mem_fiberProj]

/-!
The `n`-dimensional hypercube `Q[n]` is `n`-vertex-connected.
-/
lemma hypercube_isVertexConnected {n : ℕ} : Q[n].IsVertexConnected n := by
  induction n with
  | zero =>
    refine ⟨?_, fun S hS => absurd hS (by simp)⟩
    simp
  | succ n ih =>
    exact ih.boxProd_top_bool (hypercube_connected n)

/-!
## Vertex Connectivity Implies Edge Connectivity

A `k`-vertex-connected graph is `k`-edge-connected.

Proof sketch: Given a set `s` of less than `k` edges and vertices `u` and `v`, we
may discard the elements of `s` that are not edges of `G`. Then we pick from each
edge of `s` other than `s(u, v)` an endpoint that is neither `u` nor `v`, and let `T`
be the set of chosen endpoints (`exists_cover_avoiding`). A walk that avoids a set of
vertices meeting every edge of `s` survives the deletion of `s`
(`Walk.reachable_deleteEdges_of_avoids`). If `s(u, v)` is not one of the deleted
edges then `T` meets every deleted edge, and a walk from `u` to `v` avoiding `T`
exists by `k`-vertex-connectivity. Otherwise `T` has at most `k - 2` vertices, so
there is a vertex `w` outside `T ∪ {u, v}`, and we walk from `u` to `w` avoiding
`T ∪ {v}` and then from `w` to `v` avoiding `T ∪ {u}`; both of these sets meet every
deleted edge, including `u — v`.

Our first lemma says that given a finite set `s` of pairs `s(a, b)` with `a ≠ b`,
there is a set `T` of vertices other than `u` and `v`, with at most one vertex for
each element of `s` other than `s(u, v)`, that meets every element of `s` other than
`s(u, v)`. -/
private lemma exists_cover_avoiding [DecidableEq V] (u v : V) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, ¬ e.IsDiag) :
    ∃ T : Finset V, T.card ≤ (s.erase s(u, v)).card ∧ u ∉ T ∧ v ∉ T ∧
      ∀ e ∈ s, e ≠ s(u, v) → ∃ x ∈ e, x ∈ T := by
  have : Nonempty V := ⟨u⟩
  have hpick : ∀ e ∈ s.erase s(u, v), ∃ x ∈ e, x ≠ u ∧ x ≠ v := by
    intro e he
    obtain ⟨hne, hes⟩ := Finset.mem_erase.mp he
    have := hs e hes
    induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.mk_isDiag_iff] at this
      by_cases a = u <;> by_cases a = v <;>
        grind [Sym2.mem_mk_left, Sym2.mem_mk_right]
  choose! g hg using hpick
  refine ⟨(s.erase s(u, v)).image g, Finset.card_image_le, by grind, by grind, ?_⟩
  intro e hes hne
  have he := Finset.mem_erase.mpr ⟨hne, hes⟩
  exact ⟨g e, (hg e he).1, Finset.mem_image_of_mem _ he⟩

/-!
A walk avoiding a set `T` of vertices that meets every edge of `G` in `s` is
still a walk after deleting the edges `s`. To move the walk into the graph
`G.deleteEdges s` we use Mathlib's `Walk.toDeleteEdges`, which does this for any walk
that uses no edge of `s`.
-/
#check Walk.toDeleteEdges

lemma Walk.reachable_deleteEdges_of_avoids {s : Set (Sym2 V)} {T : Finset V}
    {x y : V} (p : G.Walk x y) (hT : ∀ e ∈ s, e ∈ G.edgeSet → ∃ z ∈ e, z ∈ T)
    (hp : ∀ z ∈ p.support, z ∉ T) : (G.deleteEdges s).Reachable x y :=
  ⟨p.toDeleteEdges s fun e he hes => by
    obtain ⟨z, hze, hzT⟩ := hT e hes (p.edges_subset_edgeSet he)
    exact hp z (p.mem_support_of_mem_edges he hze) hzT⟩

/-!
A `k`-vertex-connected graph is `k`-edge-connected.
-/
theorem IsVertexConnected.isEdgeConnected {k : ℕ} (hG : G.IsVertexConnected k) :
    G.IsEdgeConnected k := by
  classical
  intro u v s hs
  -- `s₀`: the finset of edges of `G` that lie in `s`, so `#s₀ < k`
  have hsfin : s.Finite :=
    Set.encard_lt_top_iff.mp (hs.trans (ENat.natCast_lt_top k))
  set s₀ := hsfin.toFinset.filter (· ∈ G.edgeSet)
  have hmem {e : Sym2 V} : e ∈ s₀ ↔ e ∈ s ∧ e ∈ G.edgeSet := by simp [s₀]
  have hs₀ : s₀.card < k := by
    rw [hsfin.encard_eq_coe_toFinset_card] at hs
    exact (Finset.card_filter_le _ _).trans_lt (by exact_mod_cast hs)
  obtain ⟨T, hTcard, hTu, hTv, hT⟩ := exists_cover_avoiding u v s₀
    fun e he => G.not_isDiag_of_mem_edgeSet (hmem.mp he).2
  -- a set containing `T` meets every deleted edge, except possibly `s(u, v)`
  have hcover (A : Finset V) (hA : T ⊆ A) (huv : s(u, v) ∈ s₀ → u ∈ A ∨ v ∈ A) :
      ∀ e ∈ s, e ∈ G.edgeSet → ∃ x ∈ e, x ∈ A := by
    intro e hes heG
    by_cases he : e = s(u, v)
    · subst he
      rcases huv (hmem.mpr ⟨hes, heG⟩) with h | h
      exacts [⟨u, Sym2.mem_mk_left _ _, h⟩, ⟨v, Sym2.mem_mk_right _ _, h⟩]
    · obtain ⟨x, hx, hxT⟩ := hT e (hmem.mpr ⟨hes, heG⟩) he
      exact ⟨x, hx, hA hxT⟩
  by_cases huv : s(u, v) ∈ s₀
  · -- the edge `u — v` is deleted, so `|T| ≤ k - 2`: route through a third vertex
    have hne : u ≠ v := (G.mem_edgeSet.mp (hmem.mp huv).2).ne
    have hTk : T.card + 2 ≤ k := by
      have := Finset.card_erase_add_one huv
      grind
    have hins (a : V) : (insert a T).card ≤ T.card + 1 := Finset.card_insert_le _ _
    obtain ⟨w, hw⟩ := hG.exists_notMem (insert u (insert v T)) (by
      have := hins v
      have := Finset.card_insert_le u (insert v T)
      grind)
    simp only [Finset.mem_insert, not_or] at hw
    obtain ⟨hwu, hwv, hwT⟩ := hw
    obtain ⟨p₁, hp₁⟩ := hG.exists_walk (insert v T) (by have := hins v; grind) u w
      (by simp [hne, hTu]) (by simp [hwv, hwT])
    obtain ⟨p₂, hp₂⟩ := hG.exists_walk (insert u T) (by have := hins u; grind) w v
      (by simp [hwu, hwT]) (by simp [hne.symm, hTv])
    exact (p₁.reachable_deleteEdges_of_avoids (hcover _ (Finset.subset_insert _ _)
        fun _ => .inr (Finset.mem_insert_self _ _)) hp₁).trans
      (p₂.reachable_deleteEdges_of_avoids (hcover _ (Finset.subset_insert _ _)
        fun _ => .inl (Finset.mem_insert_self _ _)) hp₂)
  · -- otherwise `T` meets every deleted edge
    have := Finset.card_erase_le (s := s₀) (a := s(u, v))
    obtain ⟨p, hp⟩ := hG.exists_walk T (by grind) u v hTu hTv
    exact p.reachable_deleteEdges_of_avoids (hcover T subset_rfl (absurd · huv)) hp

/-- The `n`-dimensional hypercube `Q[n]` is `n`-edge-connected. -/
lemma hypercube_isEdgeConnected {n : ℕ} : Q[n].IsEdgeConnected n :=
  hypercube_isVertexConnected.isEdgeConnected

/-!
## Connectivity Numbers *

The *edge connectivity* `λ(G)` of a graph is the largest `k` for which `G` is
`k`-edge-connected, and its *vertex connectivity* `κ(G)` is the largest `k` for which
`G` is `k`-vertex-connected. Neither is currently in Mathlib. We define both as
suprema in `ℕ∞`, which allows the value `⊤` when a graph is `k`-edge-connected (or
`k`-vertex-connected) for every `k`.
-/
/-- The edge connectivity of `G`: the supremum of the `k` for which `G` is
`k`-edge-connected. -/
noncomputable def edgeConnectivity (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeConnected k), (k : ℕ∞)

/-- The vertex connectivity of `G`: the supremum of the `k` for which `G` is
`k`-vertex-connected. -/
noncomputable def vertexConnectivity (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsVertexConnected k), (k : ℕ∞)

/-!
We introduce the standard notation `λ(G)` for the edge connectivity and `κ(G)` for
the vertex connectivity. Since `λ` is also Lean's keyword for `fun`, the notation
has to include the opening parenthesis: `λ(` becomes a single token, so `λ(G)` is
not read as the start of a `fun`. The price is that, wherever this notation is in
scope, a `fun` can no longer be written `λ(x : α) => …` without a space after `λ`.
-/
@[inherit_doc edgeConnectivity] scoped notation "λ(" G ")" =>
  SimpleGraph.edgeConnectivity G
@[inherit_doc vertexConnectivity] scoped notation "κ(" G ")" =>
  SimpleGraph.vertexConnectivity G

/-!
Both properties are closed under decreasing `k`, so the `k` for which `G` is
`k`-edge-connected form an initial segment of `ℕ`, and `k ≤ λ(G)` holds exactly when
`G` is `k`-edge-connected. The same holds for `κ(G)` if `V` is nonempty (the empty
graph is not even `0`-vertex-connected, yet `0 ≤ κ(G)`). The general fact is about an
`Antitone` property `P` of natural numbers, that is, one closed under decreasing `k`:
the supremum `⨆ (j) (_ : P j), j` in `ℕ∞` exceeds `k` iff `P (k + 1)` holds. It says
nothing about graphs, so we put it in the `ENat` namespace. Mathlib does not
currently have it.
-/
lemma _root_.ENat.natCast_lt_biSup_iff {P : ℕ → Prop} (hP : Antitone P) {k : ℕ} :
    (k : ℕ∞) < ⨆ (j : ℕ) (_ : P j), (j : ℕ∞) ↔ P (k + 1) := by
  simp only [lt_iSup_iff, Nat.cast_lt, exists_prop]
  exact ⟨fun ⟨j, hj, hkj⟩ => hP hkj hj, fun h => ⟨k + 1, h, k.lt_succ_self⟩⟩

/-!
The non-strict version needs `P 0` as well, since `0 ≤ ⨆ …` always holds.
-/
lemma _root_.ENat.natCast_le_biSup_iff {P : ℕ → Prop} (hP : Antitone P) (h0 : P 0)
    {k : ℕ} : (k : ℕ∞) ≤ ⨆ (j : ℕ) (_ : P j), (j : ℕ∞) ↔ P k := by
  cases k with
  | zero => simpa using h0
  | succ k =>
    rw [Nat.cast_add_one, ENat.add_one_le_iff (ENat.natCast_ne_top k)]
    exact ENat.natCast_lt_biSup_iff hP

lemma IsEdgeConnected.anti {k l : ℕ} (hkl : k ≤ l) (hG : G.IsEdgeConnected l) :
    G.IsEdgeConnected k :=
  fun u v => (hG u v).anti hkl

lemma IsVertexConnected.anti {k l : ℕ} (hkl : k ≤ l) (hG : G.IsVertexConnected l) :
    G.IsVertexConnected k :=
  ⟨le_trans (by exact_mod_cast Nat.add_le_add_right hkl 1) hG.1,
    fun S hS => hG.2 S (hS.trans_le (by exact_mod_cast hkl))⟩

/-!
Every nonempty graph is `0`-vertex-connected, but the graph with no vertices is not.
-/
lemma isVertexConnected_zero [Nonempty V] : G.IsVertexConnected 0 :=
  ⟨by simp [Order.one_le_iff_pos], fun S hS => absurd hS (by simp)⟩

lemma le_edgeConnectivity_iff {k : ℕ} :
    (k : ℕ∞) ≤ λ(G) ↔ G.IsEdgeConnected k :=
  ENat.natCast_le_biSup_iff (P := G.IsEdgeConnected) (fun _ _ hjl h => h.anti hjl)
    .zero

lemma le_vertexConnectivity_iff [Nonempty V] {k : ℕ} :
    (k : ℕ∞) ≤ κ(G) ↔ G.IsVertexConnected k :=
  ENat.natCast_le_biSup_iff (P := G.IsVertexConnected) (fun _ _ hjl h => h.anti hjl)
    isVertexConnected_zero

/-!
Since `k`-vertex-connectivity implies `k`-edge-connectivity, `κ(G) ≤ λ(G)`.
-/
theorem vertexConnectivity_le_edgeConnectivity : κ(G) ≤ λ(G) :=
  iSup₂_le fun _ hk => le_edgeConnectivity_iff.mpr hk.isEdgeConnected

/-!
Both numbers are bounded by the degree of any vertex. For `κ(G)` this is
`IsVertexConnected.le_encard_neighborSet`; for `λ(G)` we use Mathlib's
`IsEdgeConnected.le_degree`, which needs `G` to have at least two vertices.
-/
lemma vertexConnectivity_le_encard_neighborSet (v : V) :
    κ(G) ≤ (G.neighborSet v).encard :=
  iSup₂_le fun _ hk => hk.le_encard_neighborSet v

lemma edgeConnectivity_le_degree [Nontrivial V] (v : V) [Fintype (G.neighborSet v)] :
    λ(G) ≤ G.degree v :=
  iSup₂_le fun _ hk => by exact_mod_cast hk.le_degree (u := v)

/-!
Together these give *Whitney's inequalities*: a finite graph `G` with at least two
vertices satisfies `κ(G) ≤ λ(G) ≤ δ(G)`. The second inequality is
`edgeConnectivity_le_degree` at a vertex of minimum degree (Exercise 16). Both
inequalities can be strict. In the *bowtie*, two triangles sharing a vertex, deleting
the shared vertex disconnects the graph, so `κ = 1`, while `λ = δ = 2` (Exercise 17
asks you to show that `κ < λ`). Two copies of `K[4]` joined by a single edge have
`λ = 1`, since that edge is a bridge, while `δ = 3`.
-/

/-!
The two definitions disagree on graphs with at most one vertex. Mathlib's
`IsEdgeConnected k` has no condition on the number of vertices, so such a graph is
`k`-edge-connected for every `k`, whereas our `IsVertexConnected k` asks for more
than `k` vertices.
-/
lemma edgeConnectivity_of_subsingleton [Subsingleton V] : λ(G) = ⊤ :=
  ENat.eq_top_iff_forall_ge.mpr fun _ => le_edgeConnectivity_iff.mpr .of_subsingleton

lemma vertexConnectivity_of_subsingleton [Subsingleton V] : κ(G) = 0 := by
  refine (iSup₂_le fun k hk => ?_).antisymm (by simp)
  have := hk.1.trans ENat.card_le_one
  norm_cast at this ⊢; grind

/-!
# Brooks' Theorem *

The greedy bound of
[Greedy Colouring*](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-greedy-colouring)
says that a graph of maximum degree at most `Δ` is `(Δ + 1)`-colourable.
*Brooks' theorem* says exactly when this can be improved to `Δ`: a finite connected
graph of maximum degree `Δ` is `Δ`-colourable unless it is the complete graph
`K[Δ + 1]` or (when `Δ = 2`) an odd cycle. Applying this to each component, a finite
graph of maximum degree at most `Δ` is `Δ`-colourable unless it contains a
`(Δ + 1)`-clique or (when `Δ = 2`) one of its components is an odd cycle. Odd cycles
are only an obstruction when `Δ = 2`: for example the Petersen graph is cubic and
contains `5`-cycles, but it is `3`-colourable.

The cases `Δ = 2` and `Δ ≥ 3` are very different. The case `Δ = 2` follows quickly
from our characterization of bipartite graphs in
[Odd Cycles and Bipartite Graphs](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-odd-cycles-and-bipartite-graphs),
while the case `Δ ≥ 3` needs a real argument, for which we use the partial colourings
of
[Partial Colourings*](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-partial-colourings).
At the end we combine the cases into a single statement for every `Δ`.

## Maximum Degree Two

The results of
[Cycles in Graphs of Maximum Degree Two](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-cycles-in-graphs-of-maximum-degree-two)
settle the case `Δ = 2`: a graph of maximum degree at most `2` is `2`-colourable
unless one of its connected components is an odd cycle. Indeed, if it is not
`2`-colourable then it has an odd cycle, and by
`Walk.IsCycle.mem_support_of_degree_le_two` that cycle passes through every vertex of
its component. (Since every vertex has degree at most `2`, the component then has no
edges other than those of the cycle, so it *is* an odd cycle.)

We could reduce the problem to connected graphs, since a graph is `n`-colourable iff
each of its components is (`colorable_iff_forall_connectedComponent`, which glues
together colourings of the components using `homOfConnectedComponents`). But
`Walk.IsCycle.mem_support_of_degree_le_two` already works one component at a time, so
no reduction is needed.
-/
theorem brooks_two [G.LocallyFinite] (hdeg : ∀ v, G.degree v ≤ 2)
    (hcyc : ¬ ∃ (u : V) (c : G.Walk u u),
      c.IsCycle ∧ Odd c.length ∧ ∀ v, G.Reachable u v → v ∈ c.support) :
    G.Colorable 2 := by
  apply isBipartite_iff_forall_isCycle_even.mpr
  intro u c hc
  by_contra hodd
  exact hcyc ⟨u, c, hc, Nat.not_even_iff_odd.mp hodd,
    fun v huv => hc.mem_support_of_degree_le_two hdeg huv⟩

/-!
## Maximum Degree at Least Three

From now on we assume that `Δ ≥ 3`. The classical greedy colouring proof due to
Lovász (1975) uses the *blocks* of a graph, its maximal connected subgraphs without a
cut vertex, which we study in the next section,
[Cut Vertices and Blocks*](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-cut-vertices-and-blocks).
Instead, the proof we give is a variation of Lovász's approach that avoids blocks: it
uses partial colourings and the idea behind greedy colouring, but replaces the need
for 2-connected blocks with strong induction on vertex subsets and a gluing step
across a pair of non-adjacent vertices.

The basic idea is to colour vertices greedily but in an order chosen so that we never
reach an uncoloured vertex with `Δ` distinctly coloured neighbours, hence the greedy
colouring will never use more than `Δ` colours.

*Sketch Proof*: we prove the stronger statement that *every* finite subset of the
vertices `s : Finset V` satisfies `G.ColorableOn Δ ↑s`, by strong induction on `s`
under `⊂`, so our induction hypothesis is:

  `ih : ∀ t ⊂ s, G.ColorableOn Δ ↑t`.

*Degeneracy reduction:* if some `a ∈ s` has less than `Δ` neighbours in `s`, then
apply `ih` to `s.erase a` and extend the resulting colouring to `a` using a free
colour (the neighbours of `a` use less than `Δ` colours).

So wlog every vertex of `s` has at least `Δ` neighbours in `s`. Since all degrees are
at most `Δ`, every vertex of `s` must have *exactly* `Δ` neighbours, all of which lie
in `s` (so `s` is closed under adjacency).

*Regular case:* pick `v₂ ∈ s` and let `K` be the vertex set of its connected
component `G⟦v₂⟧`, which lies inside `s` since `s` is closed under adjacency. Then
`K` is closed under adjacency, so there are no edges between `K` and
`s \ K`, and we may colour `s \ K` by `ih` (it does not contain `v₂`, so it is a
proper subset) and combine this with a colouring of `K`, which we now construct. (If
`K ⊂ s` then `ih` would colour `K` as well, so the essential case is `K = s`, i.e.
`s` connected. We do not make this case split, however: the construction below works
uniformly for any adjacency-closed `Δ`-regular `K`, using only colourings of *proper*
subsets of `K`.)

Since `G` has no `Δ + 1`-clique, the neighbourhood of `v₂` is not a clique, so `v₂`
has two neighbours `v₁` and `v₃` that are not adjacent to each other. Write
`W := K \ {v₁, v₃}` for the remaining vertices of `K`. Let `A` be the vertex set of
the connected component of `v₂` in the subgraph induced by `W` (the vertices of `W`
that can be reached from `v₂` by a walk inside `W`), and let `B := W \ A` be the
rest, so there are no edges between `A` and `B`. (If the pair `{v₁, v₃}` does not
*separate* `K` then `B` is empty, but we do not need to treat this case separately.)

Now `D := A ∪ {v₁, v₃}` and `E := B ∪ {v₁, v₃}` together cover `K` and meet only in
the non-adjacent pair `{v₁, v₃}`; moreover `A`, `B` and `E` are proper subsets of
`K` (the first misses `v₁`, the others `v₂`), so `ih` applies to them. The plan is to
colour `D` and `E` separately and then glue them together using our
`ColoringOn.union` construction.

1. *`D` has a colouring in which `v₁` and `v₃` have the same colour.*

   Colour `v₁` and `v₃` first, both with colour `0` (legal, since they are not
   adjacent). Then colour the vertices of `A` other than `v₂` greedily, in
   *reverse search order from `v₂`*. That is, start with `S = {v₂}` and repeatedly
   add to `S` a vertex of `A` outside `S` that has a neighbour in `S`; we say such
   a vertex has been *settled*. Since `A` is connected, every vertex of `A` is
   eventually settled. Now colour the vertices in the reverse of the order in which
   they were settled. Each vertex was settled because of an edge to an
   already-settled neighbour, which is either `v₂` or a vertex coloured later; so
   when a vertex is coloured it still has an uncoloured neighbour, hence at most
   `Δ - 1` coloured neighbours, and a free colour exists.

   Finally colour `v₂`: among its `Δ` neighbours are `v₁` and `v₃`, which received
   the *same* colour, so its neighbours use at most `Δ - 1` colours and a free colour
   remains.

2. *Gluing.* Since the only edges from `D` to `E \ D ⊆ B` leave from `{v₁, v₃}`
   (there are no `A`–`B` edges), two colourings of `D` and `E` can be glued together
   as long as they agree on `{v₁, v₃}`. Moreover they can be made to agree by
   permuting the colours of one of them, provided that they agree on *whether* `v₁`
   and `v₃` receive equal colours. So it suffices to find colourings of `D` and `E`
   with the same *pattern* (equal or distinct) on `{v₁, v₃}`.

   By Step 1, `D` has a colouring with `v₁` and `v₃` *equal*. Also, for
   `v ∈ {v₁, v₃}` the `Δ` neighbours of `v` split between `A` and `B`, with at least
   one (namely `v₂`) in `A`.

   *Case (a).* If `v₁` and `v₃` have at most `Δ - 1` neighbours in `B` *in total*
   (as happens when `B` is empty), colour `B` by `ih` and extend to `E` giving
   `v₁, v₃` a common free colour; pair this with the equal-pattern colouring of `D`.

   *Case (b).* Otherwise one of `v₁, v₃`, say `v₁`, has at least `2` neighbours in
   `B` and hence at most `Δ - 2` in `A`. The other, `v₃`, has at most `Δ - 1`
   neighbours in `A`: since `v₂ ∈ A`, `v₁` has at most `Δ - 1` neighbours in `B`, so
   `v₃` has at least one there. So a colouring of `A` by `ih` extends to `D` giving
   `v₁, v₃` *distinct* colours. So `D` has colourings of both patterns, and we pair
   the `ih`-colouring of `E` with whichever one matches it.
-/
section brooks
variable {Δ : ℕ}
open Finset

/-!
### Free Colours and Neighbours in a Set

We start with a simple observation (an instance of Mathlib's
`Finset.exists_mem_notMem_of_card_lt_card`): less than `Δ` colours cannot exhaust
the palette `Fin Δ`.
-/
private lemma exists_color_avoiding (s : Finset (Fin Δ)) (h : #s < Δ) :
    ∃ c, c ∉ s := by
  simpa using exists_mem_notMem_of_card_lt_card (t := univ) (by simpa using h)

/-!
If the colours that `C` assigns to the neighbours of `a` lying in `s` number
less than `Δ`, then some colour `c : Fin Δ` is avoided by every neighbour of `a` in
`s`.
-/
lemma ColoringOn.exists_free_color [DecidableRel G.Adj] {s : Finset V}
    (C : G.ColoringOn (Fin Δ) ↑s) (a : V)
    (h : #({v ∈ s | G.Adj a v}.image fun v => C v) < Δ) :
    ∃ c : Fin Δ, ∀ v ∈ s, G.Adj a v → C v ≠ c := by
  obtain ⟨c, hc⟩ := exists_color_avoiding _ h
  exact ⟨c, fun v hv hadj heq =>
    hc (mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hadj⟩, heq⟩)⟩

/-!
We count the neighbours of `a` lying in a finite set `s` with `G.degIn s a`, from
[Neighbours in a Set](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-neighbours-in-a-set).
Combining `exists_free_color` with `card_image_le`: if `a` has less than `Δ`
neighbours in `s`, then the number of colours used on those neighbours is less than
`Δ`, so some colour is free for `a`.
-/
private lemma ColoringOn.exists_free_color_of_degIn [DecidableRel G.Adj]
    {s : Finset V} (C : G.ColoringOn (Fin Δ) ↑s) (a : V) (h : G.degIn s a < Δ) :
    ∃ c : Fin Δ, ∀ v ∈ s, G.Adj a v → C v ≠ c :=
  C.exists_free_color a (card_image_le.trans_lt h)

/-!
In a `(Δ + 1)`-clique-free graph, a vertex `a` of degree `Δ` has two distinct
non-adjacent neighbours (its neighbourhood is not a clique). (Notice that the
hypotheses preclude the cases `Δ = 0` and `Δ = 1` so we don't need to assume `Δ ≥ 2`
explicitly.)
-/
lemma CliqueFree.exists_ne_adj_not_adj_of_le_degree [G.LocallyFinite]
    (hcf : G.CliqueFree (Δ + 1)) {a : V} (hd : Δ ≤ G.degree a) :
    ∃ v₁ v₃, v₁ ≠ v₃ ∧ G.Adj a v₁ ∧ G.Adj a v₃ ∧ ¬ G.Adj v₁ v₃ := by
  classical
  by_contra! h
  refine hcf.mono (by grind : Δ + 1 ≤ G.degree a + 1)
    (insert a (G.neighborFinset a)) ⟨?_, ?_⟩
  · intro x hx y hy hxy
    grind [adj_symm, mem_neighborFinset]
  · rw [card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]

/-!
Mathlib lacks the converse of the following lemma, so we prove it.
-/
#check exists_ne_map_eq_of_card_image_lt
/-!
If `f` identifies two distinct elements of `s`, its image is strictly smaller
than `s`.
-/
lemma _root_.Finset.card_image_lt_card_of_ne_map_eq {W : Type*} [DecidableEq W]
    {s : Finset V} (f : V → W) {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hfab : f a = f b) : #(s.image f) < #s :=
  lt_of_le_of_ne card_image_le fun h =>
    hab (card_image_iff.mp h (mem_coe.mpr ha) (mem_coe.mpr hb) hfab)

/-!
### Step 1: Colouring in Reverse Search Order

We express "`A` is connected" as connectedness of the subgraph
`(⊤ : G.Subgraph).induce A`
([Induced Subgraphs](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-induced-subgraphs)).
Mathlib characterizes this by walks in `G` itself
(`Subgraph.connected_iff_forall_exists_walk_subgraph`): any two vertices are joined
by a walk `p` with `p.toSubgraph ≤ (⊤ : G.Subgraph).induce A`. As we saw in
[Vertex Connectivity](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-vertex-connectivity),
for an induced subgraph this just says that every vertex of `p` lies in `A`
(`Walk.toSubgraph_le_induce_top_iff`).

If the subgraph induced by `W` is connected, and `S ⊆ W` is a set of settled
vertices containing `v₂`, then some unsettled vertex has a settled neighbour: a walk
inside `W` from `v₂` to an unsettled vertex must at some point leave `S`.
-/
private lemma exists_adj_sdiff_of_connected [DecidableEq V] {W S : Finset V}
    {v₂ : V} (hconn : ((⊤ : G.Subgraph).induce (W : Set V)).Connected)
    (hv : v₂ ∈ S) (hSW : S ⊆ W) (hne : (W \ S).Nonempty) :
    ∃ z ∈ W \ S, ∃ y ∈ S, G.Adj z y := by
  obtain ⟨r, hr⟩ := hne
  obtain ⟨p, hp⟩ :=
    ((Subgraph.connected_iff_forall_exists_walk_subgraph _).mp hconn).2
      (mem_coe.mpr (hSW hv)) (mem_coe.mpr (mem_sdiff.mp hr).1)
  have hp := p.toSubgraph_le_induce_top_iff.mp hp
  obtain ⟨d, hd, hd1, hd2⟩ := p.exists_boundary_dart (↑S) (mem_coe.mpr hv)
    (by simpa using (mem_sdiff.mp hr).2)
  exact ⟨d.toProd.2, mem_sdiff.mpr
    ⟨hp _ (p.dart_snd_mem_support_of_mem_darts hd), by simpa using hd2⟩,
    d.toProd.1, by simpa using hd1, d.adj.symm⟩

/-!
The reverse-search colouring of Step 1, apart from the final step of colouring `v₂`.
For any settled set `S` with `v₂ ∈ S ⊆ W` we colour `{v₁, v₃} ∪ (W \ S)`, giving `v₁`
and `v₃` the same colour, by induction on the number of unsettled vertices.
-/
private lemma exists_coloringOn_sdiff [G.LocallyFinite] [DecidableEq V]
    (W : Finset V) (v₂ : V) {v₁ v₃ : V} (hΔ : 0 < Δ)
    (hnadj : ¬ G.Adj v₁ v₃) (hdeg : ∀ x ∈ W, G.degree x = Δ)
    (hW : Disjoint W {v₁, v₃})
    (hconn : ((⊤ : G.Subgraph).induce W).Connected) :
    ∀ (S : Finset V), v₂ ∈ S → S ⊆ W →
      ∃ C : G.ColoringOn (Fin Δ) ↑({v₁, v₃} ∪ (W \ S)), C v₁ = C v₃ := by
  classical
  suffices H : ∀ n (S : Finset V), v₂ ∈ S → S ⊆ W → #(W \ S) = n →
      ∃ C : G.ColoringOn (Fin Δ) ↑({v₁, v₃} ∪ (W \ S)), C v₁ = C v₃ by
    intro S hv hS; exact H _ S hv hS rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ hcard
    have hWS : W \ S = ∅ := card_eq_zero.mp hcard
    exact ⟨(G.coloringOnOfNotAdj hnadj ⟨0, hΔ⟩).copy (by simp [hWS]), rfl⟩
  | succ n ih =>
    intro S hv hS hcard
    have hWS : (W \ S).Nonempty := card_pos.mp (by grind)
    obtain ⟨z, hzWS, y, hyS, hadj⟩ := exists_adj_sdiff_of_connected hconn hv hS hWS
    obtain ⟨hzW, hzS⟩ := mem_sdiff.mp hzWS
    obtain ⟨C, hC⟩ := ih (insert z S) (mem_insert_of_mem hv) (insert_subset hzW hS)
      (by rw [sdiff_insert, card_erase_of_mem hzWS, hcard]; rfl)
    -- the settled neighbour `y` of `z` is still uncoloured
    have hy : y ∉ {v₁, v₃} ∪ (W \ insert z S) := by
      have := Finset.disjoint_left.mp hW (hS hyS)
      grind
    have hlt : G.degIn ({v₁, v₃} ∪ (W \ insert z S)) z < Δ := by
      have h := degIn_lt_degree_of_adj_notMem _ hadj hy
      rwa [hdeg z hzW] at h
    obtain ⟨c, hc⟩ := C.exists_free_color_of_degIn z hlt
    have hz : z ∉ ({v₁, v₃} : Finset V) := Finset.disjoint_left.mp hW hzW
    refine ⟨(C.insert z fun v hv hadj => hc v hv hadj).copy
      (by rw [← coe_insert, coe_inj]; grind), ?_⟩
    simp only [ColoringOn.coe_copy, ColoringOn.insert_apply]
    grind

/-!
The end of Step 1 of the sketch: all `Δ` neighbours of `v₂` lie in
`K.erase v₂` and are already coloured, but two of them, `v₁` and `v₃`, have the
*same* colour. So the neighbours of `v₂` use at most `Δ - 1` colours and `v₂` can be
coloured, giving a colouring of `K` in which `v₁` and `v₃` still share a colour.
-/
private lemma exists_coloringOn_insert_of_eq [DecidableEq V] [G.LocallyFinite]
    {K : Finset V} {v₁ v₂ v₃ : V} (hv₂K : v₂ ∈ K)
    (C : G.ColoringOn (Fin Δ) ↑(K.erase v₂))
    (hne13 : v₁ ≠ v₃) (hdv₂ : G.degree v₂ = Δ)
    (ha1 : G.Adj v₂ v₁) (ha3 : G.Adj v₂ v₃)
    (hnbhd : G.neighborFinset v₂ ⊆ K.erase v₂) (hcoll : C v₁ = C v₃) :
    ∃ C' : G.ColoringOn (Fin Δ) ↑K, C' v₁ = C' v₃ := by
  classical
  have hnb1 : v₁ ∈ G.neighborFinset v₂ := (mem_neighborFinset _ _ _).mpr ha1
  have hnb3 : v₃ ∈ G.neighborFinset v₂ := (mem_neighborFinset _ _ _).mpr ha3
  have hfilter : {v ∈ K.erase v₂ | G.Adj v₂ v} = G.neighborFinset v₂ := by
    rw [filter_adj_eq_inter]; exact inter_eq_left.mpr hnbhd
  have hcard : #({v ∈ K.erase v₂ | G.Adj v₂ v}.image fun v => C v) < Δ := by
    rw [hfilter]
    refine (card_image_lt_card_of_ne_map_eq _ hnb1 hnb3 hne13 hcoll).trans_le ?_
    rw [card_neighborFinset_eq_degree, hdv₂]
  obtain ⟨c, hc⟩ := C.exists_free_color v₂ hcard
  refine ⟨(C.insert v₂ (fun v hv hadj => hc v hv hadj)).copy (by simp_all), ?_⟩
  simp_all [ha1.ne.symm, ha3.ne.symm]

/-!
Step 1 of the sketch: `K` has a `Δ`-colouring giving `v₁` and `v₃` the *same* colour.
-/
private lemma exists_coloring_eq [DecidableEq V] [G.LocallyFinite] (K : Finset V)
    {v₁ v₂ v₃ : V} (hΔ : 0 < Δ)
    (hv₂K : v₂ ∈ K) (hv₁K : v₁ ∈ K) (hv₃K : v₃ ∈ K)
    (hne13 : v₁ ≠ v₃) (hnadj : ¬ G.Adj v₁ v₃) (hdv₂ : G.degree v₂ = Δ)
    (ha1 : G.Adj v₂ v₁) (ha3 : G.Adj v₂ v₃)
    (hdeg : ∀ x ∈ K \ {v₁, v₃}, G.degree x = Δ)
    (hnbhd : G.neighborFinset v₂ ⊆ K.erase v₂)
    (hconn : ((⊤ : G.Subgraph).induce (↑(K \ {v₁, v₃}) : Set V)).Connected) :
    ∃ C : G.ColoringOn (Fin Δ) ↑K, C v₁ = C v₃ := by
  classical
  have hv₂W : v₂ ∈ K \ {v₁, v₃} := mem_sdiff.mpr ⟨hv₂K, by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨ha1.ne, ha3.ne⟩⟩
  obtain ⟨C, hC⟩ := exists_coloringOn_sdiff (K \ {v₁, v₃}) v₂ hΔ hnadj hdeg
    sdiff_disjoint hconn {v₂} (mem_singleton_self v₂) (singleton_subset_iff.mpr hv₂W)
  exact exists_coloringOn_insert_of_eq hv₂K (C.copy (by rw [coe_inj]; grind))
    hne13 hdv₂ ha1 ha3 hnbhd hC

/-!
### Step 2: Gluing Along the Pair

Case (a) of Step 2. Extend a colouring of `B` by two new non-adjacent vertices
`x, y` giving them the *same* colour, when their numbers of neighbours in `B` sum to
less than `Δ`, so that together they see less than `Δ` colours.
-/
private lemma exists_two_eq [DecidableRel G.Adj] [DecidableEq V] (B : Finset V)
    (C : G.ColoringOn (Fin Δ) ↑B) {x y : V} (hnxy : ¬ G.Adj x y)
    (h : G.degIn B x + G.degIn B y < Δ) :
    ∃ C' : G.ColoringOn (Fin Δ) ↑(insert x (insert y B)), C' x = C' y := by
  classical
  have hcard : #(({v ∈ B | G.Adj x v}.image (fun v => C v)) ∪
      ({v ∈ B | G.Adj y v}.image (fun v => C v))) < Δ := by
    have hx : #({v ∈ B | G.Adj x v}.image (fun v => C v)) ≤ G.degIn B x :=
      card_image_le
    have hy : #({v ∈ B | G.Adj y v}.image (fun v => C v)) ≤ G.degIn B y :=
      card_image_le
    grind
  obtain ⟨c, hc⟩ := exists_color_avoiding _ hcard
  have hcy : ∀ v ∈ B, G.Adj y v → C v ≠ c := fun v hv hadj heq =>
    hc (mem_union_right _ (mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hadj⟩, heq⟩))
  let Cy : G.ColoringOn (Fin Δ) ↑(insert y B) :=
    (C.insert y fun v hv hadj => hcy v hv hadj).copy (by simp)
  have hCy_y : Cy y = c := by simp [Cy]
  have hCyB : ∀ v ∈ B, v ≠ y → Cy v = C v := fun v _ hv => by simp [Cy, hv]
  have hcx : ∀ v ∈ insert y B, G.Adj x v → Cy v ≠ c := by grind
  exact ⟨(Cy.insert x fun v hv hadj => hcx v hv hadj).copy (by simp), by simp [Cy]⟩

/-!
Case (b) of Step 2. Extend a colouring of `A` by two new non-adjacent vertices
`x, y` so that they receive *different* colours: `y` has less than `Δ` neighbours in
`A`, so it gets a free colour, and `x` has less than `Δ - 1`, so a free colour
distinct from that of `y` remains.
-/
private lemma exists_two_ne [DecidableRel G.Adj] [DecidableEq V] (A : Finset V)
    (C : G.ColoringOn (Fin Δ) ↑A) {x y : V} (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    (hy : G.degIn A y < Δ) (hx : G.degIn A x + 1 < Δ) :
    ∃ C' : G.ColoringOn (Fin Δ) ↑(insert x (insert y A)), C' x ≠ C' y := by
  classical
  obtain ⟨cy, hcy⟩ := C.exists_free_color_of_degIn y hy
  let Cy : G.ColoringOn (Fin Δ) ↑(insert y A) :=
    (C.insert y fun v hv hadj => hcy v hv hadj).copy (by simp)
  have hCy_y : Cy y = cy := by simp [Cy]
  have hCyA : ∀ v ∈ A, v ≠ y → Cy v = C v := fun v _ hv => by simp [Cy, hv]
  -- `x` sees the same colours among `insert y A` as in `A`
  -- (since it is not adjacent to `y`)
  have hximg : ({v ∈ insert y A | G.Adj x v}.image (fun v => Cy v)) =
      (({v ∈ A | G.Adj x v}.image (fun v => C v))) := by
    grind
  let F := ({v ∈ insert y A | G.Adj x v}.image fun v => Cy v) ∪ {cy}
  have hFcard : #F < Δ := by
    have himg : #({v ∈ A | G.Adj x v}.image (fun v => C v)) ≤ G.degIn A x :=
      card_image_le
    grind
  obtain ⟨cx, hcx⟩ := exists_color_avoiding F hFcard
  have hcx_nb : ∀ v ∈ insert y A, G.Adj x v → Cy v ≠ cx := fun v hv hadj heq =>
    hcx (mem_union_left _
      (mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hadj⟩, heq⟩))
  have hcx_cy : cx ≠ cy := fun heq =>
    hcx (mem_union_right _ (heq ▸ mem_singleton_self _))
  exact ⟨(Cy.insert x fun v hv hadj => hcx_nb v hv hadj).copy (by simp),
    by simp [Cy, Ne.symm hxy, hcx_cy]⟩


/-!
The sketch uses the set `A`: the vertices of `W := K \ {v₁, v₃}` reachable from
`v₂` by a walk inside `W`, i.e. the vertex set of the component of `v₂` in the
subgraph induced by `W`. We define this, as a `Finset`, for any finite set `W` and
record what we need: it contains `v₂` (when `v₂ ∈ W`), it is closed under adjacency
into `W`, and the subgraph it induces is connected.
-/
/-- The set of vertices of `W` reachable from `v₂` by a walk lying inside `W`. -/
noncomputable def walkComponent (G : SimpleGraph V) (v₂ : V) (W : Finset V) :
    Finset V :=
  by classical exact {a ∈ W | ∃ p : G.Walk v₂ a, ∀ y ∈ p.support, y ∈ W}

lemma mem_walkComponent {W : Finset V} {v₂ a : V} :
    a ∈ G.walkComponent v₂ W ↔
      a ∈ W ∧ ∃ p : G.Walk v₂ a, ∀ y ∈ p.support, y ∈ W := by
  simp [walkComponent]

lemma walkComponent_subset {W : Finset V} {v₂ : V} : G.walkComponent v₂ W ⊆ W := by
  simp [walkComponent]

lemma self_mem_walkComponent {W : Finset V} {v₂ : V} (h : v₂ ∈ W) :
    v₂ ∈ G.walkComponent v₂ W :=
  mem_walkComponent.mpr ⟨h, Walk.nil, by simpa using h⟩

/-!
Extending the walk to `a` along an edge `a — b` into `W` shows that `walkComponent`
is closed under adjacency into `W`.
-/
lemma adj_mem_walkComponent {W : Finset V} {v₂ a b : V}
    (ha : a ∈ G.walkComponent v₂ W) (hb : b ∈ W) (hab : G.Adj a b) :
    b ∈ G.walkComponent v₂ W := by
  obtain ⟨-, p, hp⟩ := mem_walkComponent.mp ha
  refine mem_walkComponent.mpr ⟨hb, p.concat hab, fun y hy => ?_⟩
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
  grind

/-!
Truncating the walk to `a` at its first visit to `y` shows that every vertex on
the walk lies in `walkComponent` too.
-/
lemma exists_walk_mem_walkComponent {W : Finset V} {v₂ a : V}
    (ha : a ∈ G.walkComponent v₂ W) :
    ∃ p : G.Walk v₂ a, ∀ y ∈ p.support, y ∈ G.walkComponent v₂ W := by
  classical
  obtain ⟨-, p, hp⟩ := mem_walkComponent.mp ha
  exact ⟨p, fun y hy => mem_walkComponent.mpr ⟨hp y hy, p.takeUntil y hy,
    fun z hz => hp z (p.support_takeUntil_subset_support hy hz)⟩⟩

/-!
Joining two of these walks through `v₂` shows that the subgraph induced by
`walkComponent v₂ W` is connected.
-/
lemma induce_walkComponent_connected {W : Finset V} {v₂ : V} (h : v₂ ∈ W) :
    ((⊤ : G.Subgraph).induce (G.walkComponent v₂ W : Set V)).Connected := by
  refine (Subgraph.connected_iff_forall_exists_walk_subgraph _).mpr
    ⟨⟨v₂, self_mem_walkComponent h⟩, fun {u v} hu hv => ?_⟩
  obtain ⟨p, hp⟩ := exists_walk_mem_walkComponent (mem_coe.mp hu)
  obtain ⟨q, hq⟩ := exists_walk_mem_walkComponent (mem_coe.mp hv)
  refine ⟨p.reverse.append q,
    (Walk.toSubgraph_le_induce_top_iff _).mpr fun y hy => ?_⟩
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
  exact mem_coe.mpr (hy.elim (hp y) (hq y))

/-!
In Step 2 of the sketch two colourings are made to agree on `{v₁, v₃}` by permuting
the colours of one of them. This is possible because whenever `a = b ↔ c = d`, some
permutation (a composition of at most two transpositions) maps `a` to `c` and `b` to
`d`.
-/
lemma _root_.Equiv.exists_perm_of_eq_iff_eq {α : Type*}
    {a b c d : α} (h : c = d ↔ a = b) :
    ∃ σ : Equiv.Perm α, σ a = c ∧ σ b = d := by
  classical
  exact ⟨(Equiv.swap a c).trans (Equiv.swap ((Equiv.swap a c) b) d),
          by grind, by grind⟩

/-!
Step 2 of the sketch: colourings of `D := A ∪ {v₁, v₃}` and `E := B ∪ {v₁, v₃}` with
the same pattern (equal or distinct) on `{v₁, v₃}`. Here `A` is given abstractly,
with the properties of the walk-component that we need as hypotheses, and
`B := K \ (A ∪ {v₁, v₃})`. Cases (a) and (b) of Step 2 are the two branches of the
`by_cases` split in this proof.
-/
private lemma exists_colorings_pattern_iff [DecidableEq V] [G.LocallyFinite]
    (hΔ : 3 ≤ Δ) (K A : Finset V) {v₁ v₂ v₃ : V}
    (hclosed : ∀ u ∈ K, G.neighborFinset u ⊆ K)
    (hregK : ∀ u ∈ K, G.degree u = Δ) (ih : ∀ t ⊂ K, G.ColorableOn Δ ↑t)
    (hne13 : v₁ ≠ v₃) (hnadj : ¬ G.Adj v₁ v₃)
    (ha1 : G.Adj v₂ v₁) (ha3 : G.Adj v₂ v₃)
    (hAsub : A ⊆ K \ {v₁, v₃}) (hv₂A : v₂ ∈ A)
    (hAconn : ((⊤ : G.Subgraph).induce (A : Set V)).Connected)
    (hAclosed : ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ K \ {v₁, v₃} → G.Adj a b → b ∈ A) :
    ∃ (C_D : G.ColoringOn (Fin Δ) ↑(A ∪ {v₁, v₃}))
      (C_E : G.ColoringOn (Fin Δ) ↑((K \ (A ∪ {v₁, v₃})) ∪ {v₁, v₃})),
      (C_D v₁ = C_D v₃) ↔ (C_E v₁ = C_E v₃) := by
  classical
  let B := K \ (A ∪ {v₁, v₃})
  have hv₂K : v₂ ∈ K := by grind
  have hd2 : G.degree v₂ = Δ := by grind
  have hv1K : v₁ ∈ K := hclosed v₂ hv₂K ((mem_neighborFinset _ _ _).mpr ha1)
  have hv3K : v₃ ∈ K := hclosed v₂ hv₂K ((mem_neighborFinset _ _ _).mpr ha3)
  have h13K : {v₁, v₃} ⊆ K := by grind
  have hAK : A ⊆ K := by grind
  have hv1A : v₁ ∉ A := by grind
  -- `A` and `B` partition `K \ {v₁, v₃}`.
  have hABdisj : Disjoint A B := Finset.disjoint_left.mpr
    (fun z hzA hzB => (mem_sdiff.mp hzB).2 (mem_union_left _ hzA))
  have hABcov : A ∪ B = K \ {v₁, v₃} := by grind
  -- The degree of `v₁` (resp. `v₃`) splits as its degIn `A` plus its degIn `B`
  have hNsub : ∀ v ∈ ({v₁, v₃} : Finset V), G.neighborFinset v ⊆ K \ {v₁, v₃} := by
    grind [mem_neighborFinset, adj_symm]
  have hNK : ∀ v ∈ ({v₁, v₃} : Finset V), G.degIn A v + G.degIn B v = Δ := by
    intro v hv
    rw [← degIn_union A B v hABdisj, hABcov, degIn, filter_adj_eq_inter,
      inter_eq_left.mpr (hNsub v hv),
      card_neighborFinset_eq_degree, hregK v (h13K hv)]
  have hAv1 := hNK v₁ (by grind)
  have hAv3 := hNK v₃ (by grind)
  have hA1pos : 1 ≤ G.degIn A v₁ :=
    card_pos.mpr ⟨v₂, mem_filter.mpr ⟨hv₂A, ha1.symm⟩⟩
  have hA3pos : 1 ≤ G.degIn A v₃ :=
    card_pos.mpr ⟨v₂, mem_filter.mpr ⟨hv₂A, ha3.symm⟩⟩
  -- the neighbours of `v₂` are in `D` since `A` is adjacency-closed
  have hnbhdD : G.neighborFinset v₂ ⊆ (A ∪ {v₁, v₃}).erase v₂ := by
    intro w hw
    have hwadj : G.Adj v₂ w := (mem_neighborFinset _ _ _).mp hw
    rw [mem_erase]
    exact ⟨hwadj.symm.ne, by grind⟩
  have hMA : (A ∪ {v₁, v₃}) \ {v₁, v₃} = A := by grind
  -- `D` always has a colouring with `v₁, v₃` the same colour (Step 1 applied to `D`)
  obtain ⟨C_D_eq, hC_D_eq⟩ := exists_coloring_eq (A ∪ {v₁, v₃}) (by grind)
    (mem_union_left _ hv₂A) (mem_union_right _ (by simp))
    (mem_union_right _ (by simp)) hne13 hnadj hd2 ha1 ha3
    (by grind) hnbhdD (by grind)
  have hAss : A ⊂ K := (ssubset_iff_of_subset hAK).mpr ⟨v₁, hv1K, hv1A⟩
  -- `E = B ∪ {v₁,v₃}` is a proper subset (misses `v₂ ∈ A`).
  have hv₂E : v₂ ∉ B ∪ {v₁, v₃} := by grind
  have hEss : B ∪ {v₁, v₃} ⊂ K := by grind
  by_cases hsum : G.degIn B v₁ + G.degIn B v₃ ≤ Δ - 1
  · -- Case (a): colour `B` by `ih` and give `v₁, v₃` a common free colour
    have hBss : B ⊂ K := (ssubset_iff_of_subset sdiff_subset).mpr
      ⟨v₂, hv₂K, fun h => hv₂E (mem_union_left _ h)⟩
    obtain ⟨C_B0⟩ := ih B hBss
    obtain ⟨C_E, hC_E⟩ := exists_two_eq B C_B0 hnadj (by grind)
    exact ⟨C_D_eq, C_E.copy (by grind),
      iff_of_true hC_D_eq hC_E⟩
  · -- Case (b): colour `A` by `ih` and give `v₁, v₃` distinct colours
    push Not at hsum
    obtain ⟨C_A⟩ := ih A hAss
    have hDdist : ∃ C : G.ColoringOn (Fin Δ) ↑(A ∪ {v₁, v₃}), C v₁ ≠ C v₃ := by
      by_cases h2 : 2 ≤ G.degIn B v₁
      · obtain ⟨C', hC'⟩ := exists_two_ne A C_A hne13 hnadj
          (by grind) (by grind)
        exact ⟨C'.copy (by grind), hC'⟩
      · obtain ⟨C', hC'⟩ :=
          exists_two_ne A C_A (Ne.symm hne13) (fun h => hnadj h.symm)
            (by grind) (by grind)
        exact ⟨C'.copy (by grind),
          fun h => hC' h.symm⟩
    obtain ⟨C_D_dist, hC_D_dist⟩ := hDdist
    obtain ⟨C_B0⟩ := ih _ hEss
    by_cases hBpat : C_B0 v₁ = C_B0 v₃
    · exact ⟨C_D_eq, C_B0, iff_of_true hC_D_eq hBpat⟩
    · exact ⟨C_D_dist, C_B0, iff_of_false hC_D_dist hBpat⟩

/-!
### Completing the Proof

The colouring of `K` in the regular case of the sketch: `K` is a `Δ`-regular set
containing `v₂`, closed under adjacency, with `Δ ≥ 3` and no `(Δ + 1)`-clique, and
every proper subset of `K` is `Δ`-colourable.
-/
private lemma closed_regular_case [G.LocallyFinite] (hΔ : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1))
    (K : Finset V) (v₂ : V) (hv₂ : v₂ ∈ K)
    (hclosed : ∀ u ∈ K, G.neighborFinset u ⊆ K)
    (hregK : ∀ u ∈ K, G.degree u = Δ) (ih : ∀ t ⊂ K, G.ColorableOn Δ ↑t) :
    G.ColorableOn Δ ↑K := by
  classical
  have : NeZero Δ := ⟨by grind⟩
  have hd2 : G.degree v₂ = Δ := hregK v₂ hv₂
  obtain ⟨v₁, v₃, hne13, ha1, ha3, hnadj⟩ :=
    hcf.exists_ne_adj_not_adj_of_le_degree hd2.symm.le
  have hn1 : v₁ ∈ G.neighborFinset v₂ := (mem_neighborFinset _ _ _).mpr ha1
  have hn3 : v₃ ∈ G.neighborFinset v₂ := (mem_neighborFinset _ _ _).mpr ha3
  have hv1K : v₁ ∈ K := hclosed v₂ hv₂ hn1
  have hv3K : v₃ ∈ K := hclosed v₂ hv₂ hn3
  have hv₂W : v₂ ∈ K \ {v₁, v₃} :=
     mem_sdiff.mpr ⟨hv₂, by simpa using ⟨ha1.ne, ha3.ne⟩⟩
  -- `A` is the component of `v₂` in `W = K \ {v₁, v₃}` and `B` is the rest
  let A := G.walkComponent v₂ (K \ {v₁, v₃})
  let B := K \ (A ∪ {v₁, v₃})
  have hAsub : A ⊆ K \ {v₁, v₃} := walkComponent_subset
  have hv₂A : v₂ ∈ A := self_mem_walkComponent hv₂W
  have hAclosed : ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ K \ {v₁, v₃} → G.Adj a b → b ∈ A :=
    fun a ha b hb hab => adj_mem_walkComponent ha hb hab
  -- colourings of `D` and `E` with the same pattern on `{v₁, v₃}`
  obtain ⟨C_D, C_E₀, hpat⟩ :
      ∃ (C_D : G.ColoringOn (Fin Δ) ↑(A ∪ {v₁, v₃}))
        (C_E₀ : G.ColoringOn (Fin Δ) ↑(B ∪ {v₁, v₃})),
        (C_D v₁ = C_D v₃) ↔ (C_E₀ v₁ = C_E₀ v₃) :=
    exists_colorings_pattern_iff hΔ K A hclosed hregK ih hne13 hnadj ha1 ha3
      hAsub hv₂A (induce_walkComponent_connected hv₂W) hAclosed
  -- `D ∪ E = K`.
  have hDEK : (A ∪ {v₁, v₃}) ∪ (B ∪ {v₁, v₃}) = K := by grind
  -- permute the colours of `C_E₀` so that it agrees with `C_D` on `{v₁, v₃}`
  obtain ⟨σ, hσ1, hσ3⟩ := Equiv.exists_perm_of_eq_iff_eq hpat
  let C_E : G.ColoringOn (Fin Δ) ↑(B ∪ {v₁, v₃}) := C_E₀.map σ.toEmbedding
  have hC_E_def : ∀ x, C_E x = σ (C_E₀ x) := fun _ => rfl
  -- the two colourings can be glued since they agree on `{v₁, v₃}`
  have hcompat : ∀ ⦃v w⦄, v ∈ (↑(A ∪ {v₁, v₃}) : Set V) →
      w ∈ (↑(B ∪ {v₁, v₃}) : Set V) \ ↑(A ∪ {v₁, v₃}) →
      G.Adj v w → C_D v ≠ C_E w := by
    grind [C_E₀.valid, Subgraph.induce_adj, Subgraph.top_adj]
  exact ⟨(C_D.union C_E hcompat).copy (by rw [← coe_union, hDEK])⟩

/-!
The regular case of the sketch: `K` is the set of vertices of `s` in the component
`G⟦v₂⟧`, coloured by `closed_regular_case`, and the rest `s \ K` is coloured by the
induction hypothesis.
-/
private lemma regular_case [G.LocallyFinite] [DecidableRel G.Adj] (hΔ : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1))
    (hdeg : ∀ v, G.degree v ≤ Δ) (s : Finset V) (hne : s.Nonempty)
    (hreg : ∀ a ∈ s, Δ ≤ G.degIn s a) (ih : ∀ t ⊂ s, G.ColorableOn Δ ↑t) :
    G.ColorableOn Δ ↑s := by
  classical
  obtain ⟨v₂, hv₂⟩ := hne
  have hdegs : ∀ a ∈ s, G.degree a = Δ := fun a ha =>
    (hdeg a).antisymm ((hreg a ha).trans (degIn_le_degree s a))
  have hsubs : ∀ a ∈ s, G.neighborFinset a ⊆ s := fun a ha =>
    neighborFinset_subset_of_degree_le_degIn s a ((hdeg a).trans (hreg a ha))
  -- the vertices of `s` in the connected component of `v₂`
  let K := {u ∈ s | u ∈ G⟦v₂⟧.supp}
  have hKs : K ⊆ s := filter_subset _ _
  have hmemK : ∀ {u}, u ∈ K ↔ u ∈ s ∧ u ∈ G⟦v₂⟧.supp := fun {u} => mem_filter
  have hv₂K : v₂ ∈ K := hmemK.mpr ⟨hv₂, rfl⟩
  have hclosed : ∀ u ∈ K, G.neighborFinset u ⊆ K := by
    intro u hu w hw
    have hus := hmemK.mp hu
    have hadj : G.Adj u w := (mem_neighborFinset _ _ _).mp hw
    exact hmemK.mpr ⟨hsubs u hus.1 hw,
      (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hus.2⟩
  obtain ⟨CK⟩ := closed_regular_case hΔ hcf K v₂ hv₂K hclosed
    (fun u hu => hdegs u (hKs hu))
    (fun t ht => ih t (Finset.ssubset_of_ssubset_of_subset ht hKs))
  obtain ⟨Crest⟩ := ih (s \ K) (sdiff_ssubset hKs ⟨v₂, hv₂K⟩)
  have hcompat : ∀ ⦃v w⦄, v ∈ (↑K : Set V) →
     w ∈ (↑(s \ K) : Set V) \ ↑K → G.Adj v w → CK v ≠ Crest w := by
    intro v w hv hw hadj
    have hwK : w ∈ K := hclosed v (mem_coe.mp hv) ((mem_neighborFinset ..).mpr hadj)
    exact absurd hwK (by simpa using hw.2)
  exact ⟨(CK.union Crest hcompat).copy (by simpa using hKs)⟩

/-!
Any locally finite graph that is `(Δ + 1)`-clique-free with maximum degree at most
`Δ ≥ 3` is `Δ`-colourable on any finite vertex set `s`.
-/
theorem colorableOn_of_cliqueFree [G.LocallyFinite] (hΔ : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1)) (hdeg : ∀ v, G.degree v ≤ Δ) (s : Finset V) :
    G.ColorableOn Δ ↑s := by
  classical
  induction s using strongInduction with
  | _ s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- we can use the partial colouring of the empty set since `0 < Δ`.
    exact ⟨(G.coloringOnEmpty ⟨0, by grind⟩).copy (by simp)⟩
  by_cases hex : ∃ a ∈ s, G.degIn s a < Δ
  · -- Degeneracy reduction: erase a low-degree vertex and extend greedily.
    obtain ⟨a, ha, hlt⟩ := hex
    obtain ⟨C⟩ := ih _ (erase_ssubset ha)
    have hlt' : G.degIn (s.erase a) a < Δ :=
      (degIn_mono (erase_subset a s) a).trans_lt hlt
    obtain ⟨c, hc⟩ := C.exists_free_color_of_degIn a hlt'
    exact ⟨(C.insert a (fun v hv hadj => hc v hv hadj)).copy (by simp_all)⟩
  · -- Regular case: every vertex of `s` has all `Δ` of its neighbours inside `s`.
    push Not at hex
    exact regular_case hΔ hcf hdeg s hne hex ih

/-!
*Brooks' theorem* (via greedy colouring on partial colourings). A finite graph
that is `(Δ + 1)`-clique-free with maximum degree at most `Δ ≥ 3` is `Δ`-colourable.
-/
theorem brooks [G.LocallyFinite] [Finite V] (hΔ : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1))
    (hdeg : ∀ v, G.degree v ≤ Δ) : G.Colorable Δ := by
  have := Fintype.ofFinite V
  exact (colorableOn_univ_iff_colorable G Δ).1
    (by simpa using colorableOn_of_cliqueFree hΔ hcf hdeg univ)

end brooks
/-!
By De Bruijn–Erdős, Brooks' theorem extends to infinite graphs: a locally finite
graph that is `(Δ + 1)`-clique-free with maximum degree at most `Δ ≥ 3` is
`Δ`-colourable.
-/
theorem colorable_of_cliqueFree_of_degree_le {Δ : ℕ} [G.LocallyFinite]
    (hΔ : 3 ≤ Δ) (hcf : G.CliqueFree (Δ + 1)) (hdeg : ∀ v, G.degree v ≤ Δ) :
    G.Colorable Δ :=
  colorable_of_forall_finite_subgraph_colorable fun H hH => by
    classical
    have := hH.to_subtype
    refine brooks hΔ (hcf.comap ⟨H.coeCopy⟩) fun w => ?_
    rw [Subgraph.coe_degree]
    exact (H.degree_le w).trans (hdeg w.val)

/-!
## Brooks' Theorem for Every Maximum Degree

We can now put the cases together. When `Δ ≤ 1` there is nothing to prove: a graph
with no `1`-clique has no vertices, and a graph with no `2`-clique has no edges
(`cliqueFree_one` and `cliqueFree_two`). So a graph of maximum degree at most `Δ`
with no `(Δ + 1)`-clique is `Δ`-colourable, unless `Δ = 2` and one of its components
is an odd cycle.
-/
theorem brooks_general [G.LocallyFinite] {Δ : ℕ}
    (hdeg : ∀ v, G.degree v ≤ Δ) (hcf : G.CliqueFree (Δ + 1))
    (hcyc : Δ = 2 → ¬ ∃ (u : V) (c : G.Walk u u),
      c.IsCycle ∧ Odd c.length ∧ ∀ v, G.Reachable u v → v ∈ c.support) :
    G.Colorable Δ := by
  rcases (by grind : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ 3 ≤ Δ) with rfl | rfl | rfl | hΔ
  · exact G.colorable_zero_iff.mpr (cliqueFree_one.mp hcf)
  · obtain rfl := cliqueFree_two.mp hcf
    exact ⟨Coloring.mk (fun _ => 0) fun h => h.elim⟩
  · exact brooks_two hdeg (hcyc rfl)
  · exact colorable_of_cliqueFree_of_degree_le hΔ hcf hdeg

/-!
# Cut Vertices and Blocks *

A *cut vertex* is a vertex `x` whose removal splits the connected component
containing `x` into two or more components. (For a finite graph this is the same as
saying that removing `x` increases the number of components, but that formulation
fails for graphs with infinitely many components.) A *block* of a graph `G` is a
subgraph `B` that is connected and has no cut vertex of its own, and that is maximal
among such subgraphs: no larger subgraph of `G` is both connected and free of cut
vertices. So every block is of one of three kinds: a maximal 2-connected subgraph, a
bridge (the subgraph consisting of just that edge and its two endpoints), or an
isolated vertex. One reason for caring about blocks is that they can help in
colouring a graph: for `n ≥ 1`, a graph is `n`-colourable iff each of its blocks is.
In this section we prove this for finite graphs; the exercises extend it to all
graphs.

A separate pedagogical motivation for this section is that it gives us a concrete
example of a graph-theoretic construction built from first principles using an
equivalence relation and Lean's `Quotient` type.

Mathlib does not define cut vertices. In Lean the natural definition talks about
walks rather than components: `x` is a cut vertex if some two vertices other than `x`
are joined by a walk in `G`, but every such walk passes through `x`.
-/
/-- `x` is a *cut vertex* of `G`: some two vertices other than `x` are joined by a
walk, but every walk between them passes through `x`. -/
def IsCutVertex (G : SimpleGraph V) (x : V) : Prop :=
  ∃ u v, u ≠ x ∧ v ≠ x ∧ G.Reachable u v ∧ ∀ p : G.Walk u v, x ∈ p.support

/-!
This ties cut vertices to the vertex connectivity of
[Vertex Connectivity](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-vertex-connectivity).
In the definition of `IsVertexConnected 2` the deleted set `S` has at most one
vertex. When `S` is empty the condition says that `G` is connected, and when
`S = {x}` it says (for connected `G`) that `x` is not a cut vertex. So a graph is
`2`-vertex-connected iff it has at least three vertices, is connected and has no cut
vertex.
-/
lemma isVertexConnected_two_iff : G.IsVertexConnected 2 ↔
    3 ≤ ENat.card V ∧ G.Connected ∧ ∀ x, ¬ G.IsCutVertex x := by
  have h3 : ((2 : ℕ) : ℕ∞) + 1 = 3 := by norm_num
  constructor
  · rintro ⟨hcard, h⟩
    rw [h3] at hcard
    have : Nonempty V :=
      (ENat.card_ne_zero_iff_nonempty V).mp fun h0 => by
        rw [h0] at hcard; norm_num at hcard
    refine ⟨hcard, ⟨fun u v => ?_⟩, fun x ⟨u, v, hux, hvx, _, hp⟩ => ?_⟩
    · -- deleting no vertices: `G` is connected
      obtain ⟨p, -⟩ := h ∅ (by simp) u v (by simp) (by simp)
      exact ⟨p⟩
    · -- deleting `x`: some walk from `u` to `v` avoids `x`
      obtain ⟨p, hp'⟩ :=
        h {x} (by simp) u v (by simpa using hux) (by simpa using hvx)
      exact hp' x (hp p) rfl
  · rintro ⟨hcard, hconn, hcut⟩
    refine ⟨h3 ▸ hcard, fun S hS u v hu hv => ?_⟩
    -- a set of less than two vertices is empty or a single vertex `x`
    rcases Set.encard_le_one_iff_eq.mp (by simpa using hS) with rfl | ⟨x, rfl⟩
    · obtain ⟨p⟩ := hconn u v
      exact ⟨p, by simp⟩
    · by_contra! h
      exact hcut x ⟨u, v, by simpa using hu, by simpa using hv, hconn u v,
        fun p => by obtain ⟨y, hy, rfl⟩ := h p; exact hy⟩

/-!
A cut vertex can lie in several blocks, so the blocks do not partition the vertices
of a graph, but they do partition its *edges*. So we define blocks in the same way as
connected components, via an equivalence relation, but on edges rather than vertices.
The relation we use is *cycle-equivalence*: two edges are equivalent if they are the
same edge or lie in a common cycle. The equivalence classes of this relation will be
the blocks of the graph. A bridge lies on no cycle, so it forms a block on its own.

Apart from isolated vertices, these edge classes are exactly the blocks in the sense
defined at the start of this section, though we will not prove this. An isolated
vertex lies in no edge, so it belongs to no block; in particular a graph with no
edges has no blocks at all. This is why our colouring results assume `n ≥ 1`: the
graph `K[1]` has no blocks, so all its blocks are (vacuously) `0`-colourable, but
`K[1]` is not `0`-colourable.
-/
/-- Two edges are *cycle-equivalent* if they are equal or lie on a common cycle. -/
def CycleEquivalent (G : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  e₁ = e₂ ∨ ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ e₁ ∈ c.edges ∧ e₂ ∈ c.edges

/-!
## Cycle-Equivalence

`CycleEquivalent` is reflexive by definition. It is also symmetric, and an edge that
is cycle-equivalent to an edge of `G` is itself an edge of `G`.
-/
theorem CycleEquivalent.symm {e f : Sym2 V} (h : G.CycleEquivalent e f) :
    G.CycleEquivalent f e :=
  h.imp Eq.symm fun ⟨u, p, hp, he, hf⟩ => ⟨u, p, hp, hf, he⟩

theorem CycleEquivalent.mem_edgeSet {e f : Sym2 V} (he : e ∈ G.edgeSet)
    (h : G.CycleEquivalent e f) : f ∈ G.edgeSet := by
  rcases h with rfl | ⟨_, p, _, _, hf⟩
  · exact he
  · exact p.edges_subset_edgeSet hf

/-!
`CycleEquivalent` is in fact transitive: two cycles sharing an edge `f`, one through
`e` and one through `g`, can be spliced into a single cycle through `e` and `g`.
Proving this in Lean would be painful (but not impossible); however, we can avoid
it. Mathlib allows us to form the equivalence relation *generated* by any relation.
-/
#check Relation.EqvGen
/-!
Using this we can define *block-equivalence* of edges to be the equivalence relation
*generated* by `CycleEquivalent`, which is an equivalence relation by construction.
-/

/-- Two edges are *block-equivalent* if they are related by the equivalence relation
generated by `CycleEquivalent`. -/
def BlockEquivalent (G : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  Relation.EqvGen G.CycleEquivalent e₁ e₂

/-! `BlockEquivalent` is an equivalence relation (by construction). -/
theorem blockEquivalent_equivalence : Equivalence G.BlockEquivalent :=
  Relation.EqvGen.is_equivalence _

theorem BlockEquivalent.refl (e : Sym2 V) : G.BlockEquivalent e e :=
  G.blockEquivalent_equivalence.refl e

theorem BlockEquivalent.symm {e f : Sym2 V} (h : G.BlockEquivalent e f) :
    G.BlockEquivalent f e :=
  G.blockEquivalent_equivalence.symm h

theorem BlockEquivalent.trans {e f g : Sym2 V} (h₁ : G.BlockEquivalent e f)
    (h₂ : G.BlockEquivalent f g) : G.BlockEquivalent e g :=
  G.blockEquivalent_equivalence.trans h₁ h₂

/-!
Cycle-equivalent edges are block-equivalent.
-/
theorem CycleEquivalent.blockEquivalent {e f : Sym2 V} (h : G.CycleEquivalent e f) :
    G.BlockEquivalent e f := Relation.EqvGen.rel _ _ h

/-!
Block-equivalence preserves membership in the edge set in both directions. (Notice
that we use induction on `h : G.BlockEquivalent e f` in the proof.)
-/
theorem BlockEquivalent.mem_edgeSet_iff {e f : Sym2 V} (h : G.BlockEquivalent e f) :
    e ∈ G.edgeSet ↔ f ∈ G.edgeSet := by
  induction h with
  | rel x y hxy =>
      exact ⟨fun hx => CycleEquivalent.mem_edgeSet hx hxy,
             fun hy => CycleEquivalent.mem_edgeSet hy hxy.symm⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-!
The block containing an edge `e` is the graph formed by all the edges
block-equivalent to `e`. We make it a graph of type `SimpleGraph V` on the whole
vertex type, with the vertices outside the block isolated, whereas
`ConnectedComponent.toSimpleGraph` is a graph on a subtype (see
[Which Notion of Subgraph?](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-which-notion-of-subgraph)).
This lets us compare blocks with `G` and with subgraphs of `G` using `≤`, as in
`blockOf_le` and `blockOf_mono` below.
-/
/-- The block subgraph spanned by all edges block-equivalent to `e` (as a
`SimpleGraph V`). -/
def blockOf (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
  fromEdgeSet {f | G.BlockEquivalent e f}

@[simp] theorem blockOf_adj {e : Sym2 V} {x y : V} :
    (G.blockOf e).Adj x y ↔ G.BlockEquivalent e s(x, y) ∧ x ≠ y := by
  simp [blockOf]

/-!
Every block of `G` is a subgraph of `G`.
-/
theorem blockOf_le {e : Sym2 V} (he : e ∈ G.edgeSet) : G.blockOf e ≤ G :=
  fun _ _ hab => (blockOf_adj.mp hab).1.mem_edgeSet_iff.mp he

/-!
Block-equivalent edges span the same block.
-/
theorem blockOf_eq_of_blockEquivalent {e₁ e₂ : Sym2 V}
    (h : G.BlockEquivalent e₁ e₂) : G.blockOf e₁ = G.blockOf e₂ :=
  congrArg fromEdgeSet (Set.ext fun _ => ⟨h.symm.trans, h.trans⟩)

/-!
## Blocks as a Quotient of Edges

Just as `ConnectedComponent` is the quotient of `V` by `Reachable`, a *block* is an
equivalence class of edges under `BlockEquivalent`, packaged as a quotient of
`G.edgeSet`. (Mathlib writes `ConnectedComponent` as `Quot G.Reachable`; we build
block-equivalence as a `Setoid` and use `Quotient`, but the two are interchangeable.)
The underlying subgraph `B.toGraph` of a block `B` is the lift of `blockOf` along the
quotient, which is well-defined because of `blockOf_eq_of_blockEquivalent`.

The setoid is built in two steps. First, `Relation.EqvGen.setoid G.CycleEquivalent`
bundles block-equivalence (the equivalence relation generated by `CycleEquivalent`)
as a setoid on all of `Sym2 V`. But `Sym2 V` also contains pairs that are not edges
of `G`, and we only want classes of edges. So we pull the setoid back along the
inclusion `Subtype.val : G.edgeSet → Sym2 V` using `Setoid.comap`, which relates two
edges exactly when their underlying elements of `Sym2 V` are related. We make the
result an instance, so that we can write `e ≈ f` for block-equivalent edges.
-/

/--
The setoid on edges given by block-equivalence (analogue of Mathlib's
`G.reachableSetoid`). -/
instance blockSetoid (G : SimpleGraph V) : Setoid G.edgeSet :=
  Setoid.comap Subtype.val (Relation.EqvGen.setoid G.CycleEquivalent)

/-!
Unfolding the definitions, two edges are related by `blockSetoid` exactly when they
are block-equivalent.
-/
example (e f : G.edgeSet) : e ≈ f ↔ G.BlockEquivalent e f := Iff.rfl

/-- A *block* of `G` is a block-equivalence class of edges (analogue of
`ConnectedComponent`). -/
def Block (G : SimpleGraph V) := Quotient G.blockSetoid

/-- The block containing a given edge. -/
def blockMk (G : SimpleGraph V) (e : G.edgeSet) : G.Block := Quotient.mk'' e

/-- The subgraph underlying a block: all edges block-equivalent to any
representative. Well-defined by `blockOf_eq_of_blockEquivalent`. -/
def Block.toGraph (B : G.Block) : SimpleGraph V :=
  Quotient.liftOn' B (fun e => G.blockOf ↑e) fun _ _ h =>
    G.blockOf_eq_of_blockEquivalent h

/-!
Our two definitions of a block as a `SimpleGraph V` agree.
-/
@[simp] theorem blockMk_toGraph (e : G.edgeSet) :
  (G.blockMk e).toGraph = G.blockOf ↑e := rfl

/-!
Blocks behave well under taking supergraphs and, more generally, under injective
homomorphisms: these map cycles to cycles, and hence cycle-equivalent edges to
cycle-equivalent edges.
-/
theorem CycleEquivalent.map {W : Type*} {G' : SimpleGraph W} (f : G →g G')
    (hf : Function.Injective f) {a b : Sym2 V} (h : G.CycleEquivalent a b) :
    G'.CycleEquivalent (a.map f) (b.map f) := by
  rcases h with rfl | ⟨u, c, hc, ha, hb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f u, c.map f, (Walk.isCycle_map_iff_of_injective hf).mpr hc,
      by simpa using ⟨a, ha, rfl⟩, by simpa using ⟨b, hb, rfl⟩⟩

/-!
Block-equivalence is preserved by injective homomorphisms.
-/
theorem BlockEquivalent.map {W : Type*} {G' : SimpleGraph W} (f : G →g G')
    (hf : Function.Injective f) {a b : Sym2 V} (h : G.BlockEquivalent a b) :
    G'.BlockEquivalent (a.map f) (b.map f) := by
  induction h with
  | rel x y hxy => exact (hxy.map f hf).blockEquivalent
  | refl x => exact .refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An injective homomorphism maps the block of `e` into the block of `e.map f`. -/
def blockOfHom {W : Type*} {G' : SimpleGraph W} (f : G →g G')
    (hf : Function.Injective f) (e : Sym2 V) :
    G.blockOf e →g G'.blockOf (e.map f) where
  toFun := f
  map_rel' := by
    intro x y hxy
    rw [blockOf_adj] at hxy ⊢
    exact ⟨by simpa using hxy.1.map f hf, hf.ne hxy.2⟩

/-!
A block of a subgraph is contained in the corresponding block of the larger
graph.
-/
theorem blockOf_mono {G' : SimpleGraph V} (hsub : G' ≤ G) (e : Sym2 V) :
    G'.blockOf e ≤ G.blockOf e := by
  intro x y h
  rw [blockOf_adj] at h ⊢
  exact ⟨by simpa using h.1.map (Hom.ofLE hsub) Function.injective_id, h.2⟩

/-!
## Colouring a Graph from its Blocks

The idea is to cut `G` into two pieces that share at most one vertex, colour each
piece, and glue the colourings using `Colorable.sup_of_subsingleton_inter`.
-/
#check Colorable.sup_of_subsingleton_inter
/-!
We say that `G` *splits at* `x` if it is the union of two proper subgraphs whose
supports meet in at most `x`.
-/
/-- `G` *splits at* `x` if it is the union of two proper subgraphs whose supports
meet in at most `x`. -/
def SplitsAt (G : SimpleGraph V) (x : V) : Prop :=
  ∃ G₁ G₂ : SimpleGraph V, G₁ < G ∧ G₂ < G ∧ G₁ ⊔ G₂ = G ∧
    G₁.support ∩ G₂.support ⊆ {x}

/-!
Splitting at `x` is not the same as `x` being a cut vertex. A graph with a cut vertex
`x` splits at `x`, but a graph whose edges lie in two different components splits at
every vertex, whether or not it has a cut vertex: two disjoint edges have no cut
vertex at all. Isolated vertices also play no role in `SplitsAt`. (For a connected
graph the two notions do agree.) What `SplitsAt` captures is exactly what the
colouring argument needs: `G` is glued together from two proper pieces sharing at
most one vertex. It also makes the remaining case work: a graph that splits nowhere
has all its edges in one block, whereas a graph with no cut vertex can have one block
in each of its components.

We show that a graph with a cut vertex `x` splits at `x` (`IsCutVertex.splitsAt`),
and so does a graph with edges in two different connected components, at any vertex
(`splitsAt_of_not_reachable`). Both follow from a single lemma about walks. Fix a
non-isolated vertex `u ≠ x`, and call a vertex *near* if `u` reaches it by a walk
avoiding `x`. Let `G₁` consist of the edges of `G` with a near endpoint and `G₂` of
the rest. A vertex `z ≠ x` adjacent to a near vertex is itself near, so the supports
of `G₁` and `G₂` meet in at most `x`. The edges of `G` incident to `u` lie in `G₁`,
so `G₂` is proper, and `G₁` is proper as long as some edge of `G` has no near
endpoint.
-/
theorem splitsAt_of_not_near {u x a b : V} (hux : u ≠ x) (hu : u ∈ G.support)
    (hab : G.Adj a b) (ha : ∀ p : G.Walk u a, x ∈ p.support)
    (hb : ∀ p : G.Walk u b, x ∈ p.support) : G.SplitsAt x := by
  -- `R z`: the vertex `z` is near.
  let R : V → Prop := fun z => ∃ p : G.Walk u z, x ∉ p.support
  have hR : ∀ {y z}, R y → G.Adj y z → z ≠ x → R z := by
    rintro y z ⟨p, hp⟩ hyz hzx
    exact ⟨p.concat hyz, by simp [Walk.support_concat, hp, hzx.symm]⟩
  let G₁ := G ⊓ fromRel fun y z => R y ∨ R z
  let G₂ := G ⊓ fromRel fun y z => ¬ R y ∧ ¬ R z
  obtain ⟨u', hu'⟩ := hu
  have hRu : R u := ⟨.nil, by simpa using hux.symm⟩
  have hRa : ¬ R a := fun ⟨p, hp⟩ => hp (ha p)
  have hRb : ¬ R b := fun ⟨p, hp⟩ => hp (hb p)
  refine ⟨G₁, G₂, lt_of_le_not_ge inf_le_left fun h => ?_,
    lt_of_le_not_ge inf_le_left fun h => ?_, ?_, ?_⟩
  · simpa [G₁, hRa, hRb] using h hab
  · simpa [G₂, hRu] using h hu'
  · ext y z
    refine ⟨by rintro (h | h) <;> exact h.1, fun h => ?_⟩
    by_cases hy : R y <;> by_cases hz : R z <;> simp [G₁, G₂, h, h.ne, hy, hz]
  · rintro z ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    by_contra hzx
    simp only [inf_adj, fromRel_adj, Set.mem_ofPred_eq, G₁, G₂] at hy hy'
    have hz : ¬ R z := by grind
    have : ¬ R y := fun hRy => hz (hR hRy hy.1.symm hzx)
    grind

/-!
If `x` is a cut vertex, separating `u` from `v`, then `u` and `v` are distinct, so
both are non-isolated. Every walk from `u` to a neighbour `y` of `v` passes through
`x`, since otherwise it would extend to a walk from `u` to `v` avoiding `x`. So the
edge `v — y` has no near endpoint.
-/
theorem IsCutVertex.splitsAt {x : V} (h : G.IsCutVertex x) : G.SplitsAt x := by
  obtain ⟨u, v, hux, hvx, ⟨p⟩, hp⟩ := h
  -- `u ≠ v`, since the trivial walk at `u` avoids `x`
  have huv : u ≠ v := by
    rintro rfl
    have := hp .nil
    simp only [support_nil, List.mem_singleton] at this
    exact hux this.symm
  -- so `u` and `v` both have neighbours; let `y` be a neighbour of `v`
  have hvy := p.reverse.adj_snd (not_nil_of_ne huv.symm)
  refine splitsAt_of_not_near hux (p.adj_snd (not_nil_of_ne huv)).mem_support_left
    hvy hp fun q => ?_
  -- a walk from `u` to `y` avoiding `x` would extend to one from `u` to `v`
  by_cases hyx : p.reverse.snd = x
  · exact hyx ▸ q.end_mem_support
  · simpa [support_concat, hvx.symm] using hp (q.concat hvy.symm)

/-!
If the edges `a — b` and `c — d` lie in different components, then neither endpoint
of `c — d` is near (relative to `a`, provided `a ≠ x`), and if `a = x` then we swap
the roles of the two edges.
-/
theorem splitsAt_of_not_reachable {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Reachable a c) (x : V) : G.SplitsAt x := by
  by_cases hax : a = x
  · -- take `u := c`; no walk from `c` reaches the edge `a — b`
    subst hax
    exact splitsAt_of_not_near (fun h => hac (by rw [h])) hcd.mem_support_left hab
      (fun p => (hac p.reachable.symm).elim)
      (fun p => (hac (p.concat hab.symm).reachable.symm).elim)
  · -- take `u := a`; no walk from `a` reaches the edge `c — d`
    exact splitsAt_of_not_near hax hab.mem_support_left hcd
      (fun p => (hac ⟨p⟩).elim) (fun p => (hac ⟨p.concat hcd.symm⟩).elim)

/-!
Conversely, if `G` splits at no vertex then all its edges lie in a single block. We
first show this for two edges `x — u` and `x — w` at a common vertex `x`. If some
walk from `u` to `w` avoids `x`, then shortening it to a path and closing it up with
the two edges gives a cycle through both. Otherwise every walk from `u` to `w` passes
through `x`, while `u — x — w` joins them, so `x` is a cut vertex and `G` splits at
`x`.
-/
theorem blockEquivalent_of_adj_of_adj (hG : ∀ x, ¬ G.SplitsAt x) {x u w : V}
    (hu : G.Adj x u) (hw : G.Adj x w) : G.BlockEquivalent s(x, u) s(x, w) := by
  classical
  rcases eq_or_ne u w with rfl | huw
  · exact .refl _
  by_cases h : ∃ p : G.Walk u w, x ∉ p.support
  · obtain ⟨p, hxp⟩ := h
    have hxP : x ∉ p.bypass.support :=
      fun h => hxp (p.support_bypass_subset_support h)
    -- closing up the path `p.bypass` with the edges `w — x — u` gives a cycle
    have hcyc := (cons_isCycle_iff_length_ne_one _ hu).mpr
      ⟨p.bypass_isPath.concat hxP hw.symm,
        by simpa using fun h => huw (eq_of_length_eq_zero h)⟩
    exact CycleEquivalent.blockEquivalent
      (.inr ⟨x, _, hcyc, by simp, by simp [edges_concat, Sym2.eq_swap]⟩)
  · push Not at h
    exact (hG x (IsCutVertex.splitsAt
      ⟨u, w, hu.ne.symm, hw.ne.symm, hu.symm.reachable.trans hw.reachable, h⟩)).elim

/-!
For two arbitrary edges `a — b` and `c — d` we chain the previous result along a
walk from `a` to `c`. Such a walk exists: otherwise the edges `a — b` and `c — d`
lie in different components, so `G` would split at every vertex.
-/
theorem blockEquivalent_of_not_splitsAt (hG : ∀ x, ¬ G.SplitsAt x) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) : G.BlockEquivalent s(a, b) s(c, d) := by
  have key : ∀ {y} (q : G.Walk y c) {z}, G.Adj y z →
      G.BlockEquivalent s(y, z) s(c, d) := by
    intro y q
    induction q with
    | nil => exact fun hz => blockEquivalent_of_adj_of_adj hG hz hcd
    | @cons u v _ h q ih =>
      intro z hz
      refine (blockEquivalent_of_adj_of_adj hG hz h).trans ?_
      rw [Sym2.eq_swap (a := u)]
      exact ih hcd h.symm
  by_cases hac : G.Reachable a c
  · exact key hac.some hab
  · exact (hG a (splitsAt_of_not_reachable hab hcd hac a)).elim

/-!
For finite graphs we can now argue by well-founded induction on `G`, with respect to
`<`. This is allowed because a finite type carries only finitely many graphs (a graph
is determined by its adjacency relation, `SimpleGraph.adj_injective`), and a strict
order on a finite type is well-founded. If `G` splits at some vertex, then both
pieces are proper subgraphs, whose blocks lie in blocks of `G` (`blockOf_mono`), so
we can colour them by induction and glue the colourings. Otherwise `G` is either
edgeless or equal to the block of any of its edges.
-/
theorem colorable_of_forall_block [Finite V] {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph V) (hcol : ∀ B : G.Block, B.toGraph.Colorable n) :
    G.Colorable n := by
  have : Finite (SimpleGraph V) := .of_injective _ SimpleGraph.adj_injective
  induction G using WellFoundedLT.induction with
  | _ G ih =>
    have hlt : ∀ H < G, H.Colorable n := fun H hH => ih H hH fun B => by
      induction B using Quotient.inductionOn' with
      | h e =>
        exact (hcol (G.blockMk ⟨e, edgeSet_mono hH.le e.2⟩)).mono_left
          (blockOf_mono hH.le e)
    by_cases hs : ∃ x, G.SplitsAt x
    · obtain ⟨x, G₁, G₂, h₁, h₂, hG, hmeet⟩ := hs
      rw [← hG]
      exact Colorable.sup_of_subsingleton_inter hmeet (hlt _ h₁) (hlt _ h₂)
    · push Not at hs
      by_cases he : ∃ a b, G.Adj a b
      · obtain ⟨a, b, hab⟩ := he
        exact (hcol (G.blockMk ⟨s(a, b), hab⟩)).mono_left fun c d hcd =>
          blockOf_adj.2 ⟨blockEquivalent_of_not_splitsAt hs hab hcd, hcd.ne⟩
      · push Not at he
        exact ⟨Coloring.mk (fun _ => (⟨0, hn⟩ : Fin n)) fun {a b} hab =>
          (he a b hab).elim⟩

/-!
In the exercises we use the *De Bruijn–Erdős theorem* (see
[De Bruijn–Erdős Theorem](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-de-bruijn-erd-s-theorem))
to remove the finiteness assumption: for `n ≥ 1`, any graph is `n`-colourable iff
each of its blocks is.
-/

end SimpleGraph
