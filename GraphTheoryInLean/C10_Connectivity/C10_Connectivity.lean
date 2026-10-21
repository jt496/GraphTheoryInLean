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
In this chapter we study graph connectivity. Building on the reachability relation
`Reachable`, we start with Mathlib's notions `Preconnected` and `Connected`,
connected components and bridges, and show that the Mycielskian `mμ[G]` is connected
iff `G` has no isolated vertices, and that in a graph of maximum degree at most `2`
every cycle is its own connected component. We then look at trees, and show that the
infinite path `pathNat₁` is one. We prove *Euler's theorem*: a finite graph has an
Eulerian trail iff all its edges lie in one component and it has either no vertex of
odd degree or exactly two. Next we introduce Mathlib's edge connectivity
(`IsEdgeConnected`), and give our own definition of vertex connectivity
(`IsVertexConnected`). We show that `k`-vertex-connectivity implies
`k`-edge-connectivity. We also define the edge and vertex connectivity of a graph as
numbers in `ℕ∞` and prove Whitney's inequalities.

The final two sections are more advanced. We prove *Brooks' theorem*: a locally
finite graph of maximum degree at most `Δ` is `Δ`-colourable unless it contains a
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
#source Connected     -- structure Connected : Prop where
                      --   protected preconnected : G.Preconnected
                      --   protected [nonempty : Nonempty V]

/-!
## Connected Graphs

The two notions differ only for the graph on an empty vertex type. This graph is
vacuously preconnected, but it is not connected. With this convention a graph is
connected exactly when it has precisely one connected component; the graph with no
vertices has none.
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
example (h : G.Connected) {u v : V} : G.Reachable u v := h u v

/-!
The hypercube is connected: we can use the Hamming path to walk between any two
vertices, and we already gave a `Nonempty` instance for its vertices which Lean will
find automatically.
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
A connected graph has a path between any two vertices.
-/
#check Connected.exists_isPath

/-!
A graph is connected iff there is a vertex `v` from which every other vertex is
reachable.
-/
#check connected_iff_exists_forall_reachable

/-!
In the Mycielskian of a graph `G`, any vertex `u` that is not isolated in `G` has
both its left and right copies in `mμ[G]` connected to `none`. Given the edge `u — v`
in `G` we have the walks `u ᵣ — none` and `u ₗ — v ᵣ — none` in `mμ[G]`. Conversely
if `u` is an isolated vertex in `G` then `u ₗ` is an isolated vertex in `mμ[G]`.

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
Two components are equal iff they are constructed from reachable vertices.
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
A connected graph has exactly one component. We state this with `Nat.card`, so it
applies to infinite graphs too. Mathlib's
`Preconnected.subsingleton_connectedComponent` says that there is at most one
component, and a connected graph is nonempty, so there is at least one
(`Nat.card_eq_one_iff_unique`).
-/
lemma Connected.card_connectedComponent (h : G.Connected) :
    Nat.card G.ConnectedComponent = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨h.preconnected.subsingleton_connectedComponent,
    h.nonempty.map G.connectedComponentMk⟩

/-!
Conversely, a graph with exactly one component is connected: any two vertices lie in
the same component, and the graph is nonempty since that component has a
representative vertex (`ConnectedComponent.out`).
-/
lemma connected_iff_card_connectedComponent :
    G.Connected ↔ Nat.card G.ConnectedComponent = 1 := by
  refine ⟨Connected.card_connectedComponent, fun h => ?_⟩
  obtain ⟨_, ⟨C⟩⟩ := Nat.card_eq_one_iff_unique.mp h
  have : Nonempty V := ⟨C.out⟩
  exact ⟨fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)⟩

/-!
In informal graph theory we often think of a connected component as a graph, or
subgraph, or subset of the vertex set of the original graph. But in Lean a connected
component `C : G.ConnectedComponent` is none of these: it is an element of the
*quotient type* `G.ConnectedComponent` of `V` by the equivalence relation
`Reachable`, that is, an equivalence class of vertices. However we can convert a
connected component into all of these things.

The *support* of a component is the set of vertices in that component.
-/
#check ConnectedComponent.supp --  (C : G.ConnectedComponent) : Set V
/-!
The `SimpleGraph` and `Subgraph` given by a component are `C.toSimpleGraph` and
`C.toSubgraph`.
-/
#source ConnectedComponent.toSimpleGraph -- .. SimpleGraph C := G.induce C.supp
#source ConnectedComponent.toSubgraph    -- .. G.Subgraph := Subgraph.induce ⊤ C.supp

/-!
Connectivity of a `G.Subgraph` is a separate notion, defined via the coercion of the
subgraph to a `SimpleGraph` on its vertex set. This is one of the duplications
discussed in
[Duplication](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-duplication);
we will use it in the proof of Brooks' theorem.

The subgraph of a connected component is connected.
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
need to `2`-colour each component" since if we have `2`-colourings for each component
of a graph we can combine them into a `2`-colouring of the whole graph. This is more
generally true for homomorphisms.
-/
#check homOfConnectedComponents

/-!
Recall our definition of a `SimpleGraph.sigma` graph: the disjoint union of an
indexed family of graphs.
-/
#check SimpleGraph.sigma
/-!
There is a natural isomorphism between a graph and the sigma graph of its connected
components, sending a vertex `v` to the pair `⟨G⟦v⟧, v⟩`. Informally this is
obvious, but in Lean we meet again the cast `h ▸ w` from the definition of `Σg`
(`SimpleGraph.sigma`): the images of `v` and `w` are adjacent
when there is a proof `h : G⟦v⟧ = G⟦w⟧` such that `v` is adjacent to `h ▸ w` in
`G⟦v⟧.toSimpleGraph`. The cast is stuck until `h` is substituted away, and here
we cannot do that: `subst` needs one side of the equation to be a variable, but
`G⟦v⟧` and `G⟦w⟧` are terms.

One solution is to prove the adjacency rule once, for indices that *are* variables. A
component's graph `C.toSimpleGraph` is by definition the induced graph
`G.induce C.supp`, so it is enough to describe adjacency in a sigma graph of induced
graphs: `⟨i, u⟩` and `⟨j, v⟩` are adjacent iff `i = j` and `u` and `v` are adjacent
in `G`. This statement involves no cast, and in its proof the pattern `rfl`
substitutes `i = j` away, since `i` and `j` are variables.
-/
lemma sigma_induce_adj {ι : Type*} {S : ι → Set V} {i j : ι} {u : S i} {v : S j} :
    (Σg fun i => G.induce (S i)).Adj ⟨i, u⟩ ⟨j, v⟩ ↔ i = j ∧ G.Adj u v := by
  constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩

/-!
In the isomorphism the condition `G⟦v⟧ = G⟦w⟧` is then automatic, since adjacent
vertices lie in the same component
(`ConnectedComponent.connectedComponentMk_eq_of_adj`). The proof of `right_inv` uses
the same substitution idea: a vertex of the sigma graph is a component `C` together
with a vertex `v` and a proof of `v ∈ C`, which by definition says `G⟦v⟧ = C`, and
since `C` is a variable the pattern `rfl` substitutes it.
-/
/-- The isomorphism between `G` and the sigma graph of its connected components. -/
def isoSigmaConnectedComponents :
    G ≃g Σg (fun C : G.ConnectedComponent => C.toSimpleGraph) where
  toFun v := ⟨G⟦v⟧, ⟨v, rfl⟩⟩
  invFun p := p.2
  left_inv v := rfl
  right_inv := by
    rintro ⟨_, ⟨v, rfl⟩⟩
    rfl
  map_rel_iff' := sigma_induce_adj.trans
    ⟨And.right, fun h => ⟨ConnectedComponent.connectedComponentMk_eq_of_adj h, h⟩⟩

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
Recall from `isCycle_mycielskianClosed_of_adj` that any edge `u — v` in a graph
gives rise to a `5`-cycle in its Mycielskian.
-/
#check isCycle_mycielskianClosed_of_adj

/-!
So every edge of `mμ[G]` that comes from an edge of `G` lies on a `5`-cycle, and so
does the edge `none — u ᵣ` whenever `u` has a neighbour `v` in `G`. None of these
edges is a bridge. On the other hand, if `u` is isolated in `G` then `none` is the
only neighbour of `u ᵣ`, so deleting the edge `none — u ᵣ` cuts `u ᵣ` off. Hence the
bridges of `mμ[G]` are precisely the edges `none — u ᵣ` where `u` is an isolated
vertex of `G`.

[Figure: Left: a graph $G$ with an isolated vertex $u$. Right: its Mycielskian, whose only bridge is the edge from the apex $\ast$ to $u_r$ (orange)](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_bridge.svg)
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
      -- split on the types of the endpoints; `simp only` discharges the four pairs
      -- that are never edges: `none — none`, `none — v ₗ`, `u ₗ — none`, `u ᵣ — v ᵣ`
      rcases x with _ | (u | u) <;>
        rcases y with _ | (v | v) <;> simp only [mycielskian_adj] at hxy
      · -- `none — v ᵣ`: a neighbour `w` of `v` would put `e` on a `5`-cycle, so `v`
        -- is isolated
        exact ⟨v, fun w hw => hncyc (isCycle_mycielskianClosed_of_adj hw.symm)
          (by simp [Sym2.eq_swap, Walk.mycielskian]), rfl⟩
      · -- `u ₗ — v ₗ`: impossible, it lies on the `5`-cycle of the edge `u — v`
        exact (hncyc (isCycle_mycielskianClosed_of_adj hxy)
          (by simp [Walk.mycielskian])).elim
      · -- `u ₗ — v ᵣ`: impossible, it lies on the `5`-cycle of the edge `u — v`
        exact (hncyc (isCycle_mycielskianClosed_of_adj hxy)
          (by simp [Walk.mycielskian])).elim
      · -- `u ᵣ — none`: as in the first case, `u` is isolated
        exact ⟨u, fun w hw => hncyc (isCycle_mycielskianClosed_of_adj hw.symm)
          (by simp [Sym2.eq_swap, Walk.mycielskian]), Sym2.eq_swap⟩
      · -- `u ᵣ — v ₗ`: impossible, it lies on the `5`-cycle of the edge `v — u`
        exact (hncyc (isCycle_mycielskianClosed_of_adj hxy.symm)
          (by simp [Sym2.eq_swap, Walk.mycielskian])).elim
  · rintro ⟨u, hiso, rfl⟩
    rw [isBridge_iff]
    -- `u` is isolated in `G`, so `none` is the only neighbour of `u ᵣ`: once the
    -- edge `none — u ᵣ` is deleted, `u ᵣ` has no neighbours at all
    have hnb : ∀ w, ¬ (mμ[G].deleteEdges {s(none, u ᵣ)}).Adj (u ᵣ) w := by
      rintro (_ | w | w) h <;> simp_all [Sym2.eq_swap, IsIsolated]
    -- so a walk from `u ᵣ` to `none` has nowhere to take its first step
    intro h
    obtain ⟨p⟩ := h.symm
    cases p with
    | cons hadj _ => exact hnb _ hadj

/-!
## Cycles in Graphs of Maximum Degree Two

In a graph in which every vertex has degree at most `2`, a cycle is an entire
connected component. The key observation: at a vertex `x` of a cycle `c`, the cycle
already uses every edge of `G` at `x`. Indeed, `x` has two neighbours on the cycle
(`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`) and at most two in `G`, so the
first set of neighbours, being contained in the second, is all of it
(`Set.eq_of_subset_of_ncard_le`).
-/
lemma Walk.IsCycle.neighborSet_toSubgraph_eq_of_degree_le_two [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ 2) {u x : V} {c : G.Walk u u} (hc : c.IsCycle)
    (hx : x ∈ c.support) : c.toSubgraph.neighborSet x = G.neighborSet x :=
  Set.eq_of_subset_of_ncard_le (fun _ h => c.toSubgraph.adj_sub h)
    (by grind [ncard_neighborSet, hc.ncard_neighborSet_toSubgraph_eq_two hx])

/-!
Hence a vertex lies on the cycle iff it is reachable from it, that is, a cycle passes
through every vertex of its connected component. One direction holds for any walk
(`Walk.takeUntil`). For the other, if some vertex reachable from the cycle `c` lay
off it, then some edge `y — z` of a walk to it would leave the cycle, with
`y ∈ c.support` and `z ∉ c.support` (`Walk.exists_boundary_dart`). But every
neighbour of `y` in `G` is a neighbour of `y` on the cycle, so `z` would lie on the
cycle after all.
-/
lemma Walk.IsCycle.mem_support_iff_reachable_of_degree_le_two [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ 2) {u v : V} {c : G.Walk u u} (hc : c.IsCycle) :
    v ∈ c.support ↔ G.Reachable u v := by
  refine ⟨fun hv => by classical exact ⟨c.takeUntil v hv⟩, fun huv => ?_⟩
  by_contra hv
  obtain ⟨d, -, hd₁, hd₂⟩ :=
    huv.some.exists_boundary_dart {x | x ∈ c.support} c.start_mem_support hv
  have : d.snd ∈ c.toSubgraph.neighborSet d.fst := by
    rw [hc.neighborSet_toSubgraph_eq_of_degree_le_two hdeg hd₁]
    exact d.adj
  exact hd₂ (c.mem_support_of_adj_toSubgraph this.symm)

/-!
Together, these two lemmas say that the cycle *is* its connected component, as
subgraphs of `G`.
-/
theorem Walk.IsCycle.toSubgraph_eq_of_degree_le_two [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ 2) {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    c.toSubgraph = G⟦u⟧.toSubgraph := by
  have hmem (x : V) := hc.mem_support_iff_reachable_of_degree_le_two hdeg (v := x)
  ext x y
  · simp [hmem, ConnectedComponent.eq, reachable_comm]
  · simp only [Subgraph.induce_adj, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq, Subgraph.top_adj, reachable_comm (v := u), ← hmem]
    refine ⟨fun h => ⟨c.mem_support_of_adj_toSubgraph h,
      c.mem_support_of_adj_toSubgraph h.symm, h.adj_sub⟩,
      fun ⟨hx, _, hxy⟩ => ?_⟩
    rw [← Subgraph.mem_neighborSet,
      hc.neighborSet_toSubgraph_eq_of_degree_le_two hdeg hx]
    exact hxy

/-!
In particular, every cycle in a connected graph of maximum degree at most `2` is a
*Hamiltonian cycle* (`Walk.IsHamiltonianCycle`): the tail of a cycle is a path
(`Walk.IsCycle.isPath_tail`), and a path through every vertex is Hamiltonian
(`Walk.IsPath.isHamiltonian_of_mem`).
-/
lemma Walk.IsCycle.isHamiltonianCycle_of_degree_le_two [DecidableEq V]
    [G.LocallyFinite] (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) : c.IsHamiltonianCycle :=
  ⟨hc, hc.isPath_tail.isHamiltonian_of_mem fun v => by
    rw [support_tail_of_not_nil _ hc.not_nil, mem_support_tail_iff hc.not_nil]
    exact (hc.mem_support_iff_reachable_of_degree_le_two hdeg).mpr (hconn u v)⟩

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
## The Infinite Path is a Tree

Our running example `pathNat₁` is a tree. It is connected, since every vertex `n` can
be reached from `0` along the walk `pathNat₁Walk 0 n`. This walk ends at `0 + n`,
which is not definitionally `n`, so we use `Walk.copy`
([Copy](https://jt496.github.io/GraphTheoryInLean/Walks/#section-copy)) to change its
endpoint.
-/
lemma pathNat₁_connected : pathNat₁.Connected :=
  (connected_iff_exists_forall_reachable _).2
    ⟨0, fun n => ⟨(pathNat₁Walk 0 n).copy rfl (by simp)⟩⟩

/-!
To see that `pathNat₁` is acyclic, consider the largest vertex `m` of a cycle. It has
two neighbours on the cycle (`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`), but
its only neighbour that is not larger than `m` is `m - 1`.
-/
lemma pathNat₁_isAcyclic : pathNat₁.IsAcyclic := by
  intro v c hc
  -- let `m` be the largest vertex of the cycle `c`
  obtain ⟨m, hm, hmax⟩ := c.support.toFinset.exists_max_image id ⟨v, by simp⟩
  simp only [List.mem_toFinset, id] at hm hmax
  -- its cycle neighbours are adjacent to `m` and at most `m`, so equal `m - 1`
  have hsub : c.toSubgraph.neighborSet m ⊆ {m - 1} := fun w hw => by
    have := c.toSubgraph.adj_sub hw
    have := hmax w (c.mem_support_of_adj_toSubgraph hw.symm)
    grind
  -- but `m` has two neighbours on the cycle
  have := Set.ncard_le_ncard hsub
  rw [hc.ncard_neighborSet_toSubgraph_eq_two hm, Set.ncard_singleton] at this
  grind

lemma pathNat₁_isTree : pathNat₁.IsTree := ⟨pathNat₁_connected, pathNat₁_isAcyclic⟩

/-!
## The Edge Count Formula

A tree on `n` vertices has exactly `n - 1` edges. Mathlib states this as
`#G.edgeFinset + 1 = Fintype.card V`, which avoids the truncated subtraction of `ℕ`:
working with `n - 1` would need the side condition `1 ≤ n`.
-/
#check IsTree.card_edgeFinset -- #G.edgeFinset + 1 = Fintype.card V

/-!
Conversely, a finite connected graph with this many edges is a tree.
-/
#check isTree_iff_connected_and_card

/-!
More generally, a connected graph satisfies `|V| ≤ |E(G)| + 1`. This is stated with
`Nat.card`, so it needs no finiteness assumption, but for an infinite graph it says
nothing useful: `Nat.card` of an infinite type is the junk value `0`, so for
`pathNat₁` it says `0 ≤ 0 + 1`.
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

example {n : ℕ} : pathNat₁.IsBridge s(n, n + 1) :=
  isAcyclic_iff_forall_adj_isBridge.mp pathNat₁_isAcyclic (by simp)

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
# Eulerian Circuits and Trails

Mathlib has the necessary conditions in Euler's theorem (see
[Eulerian Trails](https://jt496.github.io/GraphTheoryInLean/Walks/#section-eulerian-trails)),
but not the existence direction: a connected graph with all degrees even has an
Eulerian circuit, and a connected graph with exactly two vertices of odd degree has
an Eulerian trail. We prove these here with a splicing argument in the style of
*Hierholzer's algorithm*. Rather than running the algorithm we take a longest trail
and show that, if it were not Eulerian, we could splice a circuit into it to make it
longer.

A standard proof might typically prove this for the all-even circuit case first and
then argue that the open trail case reduces to the closed circuit case by adding a
new vertex and two new edges from the odd-degree vertices to the new vertex. This
would definitely be possible in Lean, but somehow more complicated than necessary.
Instead we prove the open case directly, reusing code from the circuit case.

Euler's theorem is often stated for connected graphs, but, as we saw in
[Eulerian Trails](https://jt496.github.io/GraphTheoryInLean/Walks/#section-eulerian-trails),
`IsEulerian` ignores isolated vertices. The analogous necessary condition is that all
the edges of `G` lie in a single connected component. We make this a definition
`EdgesInOneComponent`. This is the weakest hypothesis under which the Eulerian
existence theorems below hold, strictly weaker than `Connected`, which also forbids
isolated vertices (when there are at least two vertices) and the graph with no
vertices.
-/
/-- Every edge of `G` lies in a single connected component: any two non-isolated
vertices are reachable from each other. -/
def EdgesInOneComponent (G : SimpleGraph V) : Prop :=
  ∀ u ∈ G.support, ∀ v ∈ G.support, G.Reachable u v

/-!
A connected graph has all its edges in one component (indeed all its vertices are
mutually reachable). This allows the Eulerian existence results to be stated for the
weaker `EdgesInOneComponent` and recovered for `Connected` as corollaries.
-/
lemma Connected.edgesInOneComponent (h : G.Connected) : G.EdgesInOneComponent :=
  fun u _ v _ => h u v

section EulerExistence

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
#check Walk.IsEulerian.connected_of_forall_not_isIsolated

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
`locallyFiniteDeleteEdges` until the end of this section and nowhere else.
-/
attribute [local instance] locallyFiniteDeleteEdges

/-!
## Extending Trails

In an all-even-degree graph, a trail that has not returned to its start can be
extended: its current endpoint `w` is incident to an edge the trail has not used.
(The number of edges in the trail that are incident to `w` is odd, while `degree w`
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
`exists_unused_edge_of_even` until it returns to `v`. The proof applies
`exists_closed_isTrail_length_le` recursively to longer trails. It isn't obvious to
Lean that this is well-founded so we need to give a termination argument.

We know that no trail is longer than the number of edges in the graph
(`IsTrail.length_le_card_edgeFinset`), and the trail in the recursive call is
strictly longer than the original trail `p`, so the measure
`Nat.card G.edgeSet - p.length` strictly decreases with each recursive call. This is
what we are doing in the `termination_by` and `decreasing_by` section below. The
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
`G.degree x` at every vertex, then every degree in the graph formed by deleting the
edges of `p` is even.
-/
lemma IsTrail.even_degree_deleteEdges {u v} {p : G.Walk u v} (hp : p.IsTrail)
    (hpar : ∀ x, Even (p.edges.countP (fun e => x ∈ e)) ↔ Even (G.degree x)) :
    ∀ x, Even ((G.deleteEdges {e | e ∈ p.edges}).degree x) := by
  intro x
  have hinc : (G.deleteEdges {e | e ∈ p.edges}).incidenceFinset x
            = (G.incidenceFinset x).filter (· ∉ p.edges) := by
    ext e
    grind [mem_incidenceFinset, incidenceSet, edgeSet_deleteEdges]
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
  have hGab : Gp.Adj a b := by grind [deleteEdges_adj]
  have hpos : ∀ {x y}, Gp.Adj x y → 0 < Gp.degree x :=
    fun {x y} hxy => (Gp.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
  by_cases ha : a ∈ p.support
  · exact ⟨a, ha, hpos hGab⟩
  · obtain ⟨q⟩ := hG a hab.left_mem_support u hu
    obtain ⟨⟨⟨c, d⟩, hcd⟩, -, ⟨hc, hd⟩⟩ :=
      q.reverse.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support ha
    have hcd_notin : s(c, d) ∉ p.edges :=
      fun hmem => hd (p.snd_mem_support_of_mem_edges hmem)
    have hcdGp : Gp.Adj c d := by grind [deleteEdges_adj]
    exact ⟨c, hc, hpos hcdGp⟩

/-!
To *splice* a closed walk `c` at `w` into a walk `p` through `w`, we split `p` as
`(p.takeUntil w) ++ (p.dropUntil w)` and insert `c` to get
`(p.takeUntil w) ++ c ++ (p.dropUntil w)`. The result has length
`p.length + c.length`, and if `p` and `c` are trails with no common edges then it is
again a trail.

[Figure: Hierholzer's splicing step on $K_5$: splice a new circuit $c$ (red, centre) at $w$ into the circuit $p$ (blue, left) starting at $v$, to obtain an Eulerian circuit starting at $w$ (right)](https://jt496.github.io/GraphTheoryInLean/figures/hierholzer.svg)
-/
omit [G.LocallyFinite] in
lemma IsTrail.takeUntil_append_append_dropUntil {a b w : V} {p : G.Walk a b}
    (hp : p.IsTrail) (hw : w ∈ p.support) {c : G.Walk w w} (hc : c.IsTrail)
    (hdisj : List.Disjoint c.edges p.edges) :
    ((p.takeUntil w hw).append (c.append (p.dropUntil w hw))).IsTrail := by
  simp only [isTrail_append, edges_append]
  refine ⟨hp.takeUntil hw, ⟨hc, hp.dropUntil hw, ?_⟩, ?_⟩
  · -- the edges of `c` are disjoint from the `w → b` part of `p`
    exact fun e he hf => hdisj he (edges_dropUntil_subset_edges p hw hf)
  · -- the `a → w` part of `p` is disjoint from both `c` and the `w → b` part
    intro e het he'
    rcases List.mem_append.mp he' with hec | hed
    · exact hdisj hec (edges_takeUntil_subset_edges p hw het)
    · exact hp.disjoint_edges_takeUntil_dropUntil hw het hed

omit [G.LocallyFinite] in
lemma length_takeUntil_append_append_dropUntil {a b w : V} (p : G.Walk a b)
    (hw : w ∈ p.support) (c : G.Walk w w) :
    ((p.takeUntil w hw).append (c.append (p.dropUntil w hw))).length =
      p.length + c.length := by
  have hsp := congrArg Walk.length (p.take_spec hw)
  grind [length_append]

variable [Finite G.edgeSet]
/-!
A non-Eulerian trail `p` from `a` to `b` can be extended, provided every vertex has
even degree in the graph obtained by deleting the edges of `p`. Find a vertex `w` on
`p` incident to an unused edge, build a circuit `c` at `w` in the
deleted graph, transfer it back into `G`, and splice it into `p` at `w`.

[Figure: Splicing a closed trail $c$ (red, centre) at $w$ into a trail $p$ (blue, left) from $a$ to $b$ gives a longer trail from $a$ to $b$ (right)](https://jt496.github.io/GraphTheoryInLean/figures/euler_two_odd.svg)

Notice that this lemma will allow us to handle both the closed case (`a = b`, the
Eulerian *circuit*, where the parity hypothesis `hdel` comes from
`IsTrail.even_degree_deleteEdges_closed`) and the open case (`a ≠ b`, the Eulerian
*trail*, where it comes from `IsTrail.even_degree_deleteEdges_open`).
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
  have hc_notin : List.Disjoint (c.transfer G htr).edges p.edges := by
    intro e he hpe
    rw [edges_transfer] at he
    grind [edgeSet_deleteEdges, c.edges_subset_edgeSet he]
  -- splice `c` into `p` at `w`: walk `a → w`, then around `c`, then `w → b`. This
  -- is a strictly longer trail from `a` to `b`.
  refine ⟨_, hp.takeUntil_append_append_dropUntil hw_supp (hc.isTrail.transfer htr)
    hc_notin, ?_⟩
  grind [length_takeUntil_append_append_dropUntil, length_transfer,
         hc.three_le_length]

/-!
## Euler's Theorem

Both cases of Euler's theorem now follow. Let `q` be a longest trail from `a` to `b`
(trails have length at most `#G.edgeFinset`, so one exists as soon as there is any
trail `q₀` from `a` to `b`). If `q` were not Eulerian then
`IsTrail.exists_longer_of_not_isEulerian` would give a longer trail, a contradiction.
The two cases differ only in why deleting the edges of a trail leaves every degree
even, so we take this as the hypothesis `hdel`.
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
*Euler's theorem* (existence direction, circuit): a graph with finitely many edges,
all in one component (`EdgesInOneComponent`), in which every vertex has even degree
has an Eulerian circuit. `[Nonempty V]` is needed only so that we can name a start
vertex in the case that the graph has no edges.
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
*Euler's theorem* (existence direction, circuit) for a *connected* graph: recovered
from `exists_isEulerian_circuit` via `Connected.edgesInOneComponent`.
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
*Euler's theorem* (existence direction, open trail) for a *connected* graph:
recovered from `exists_isEulerian_trail_of_two_odd` via
`Connected.edgesInOneComponent`.
-/
theorem _root_.SimpleGraph.Connected.exists_isEulerian_trail {a b} (h : G.Connected)
    (hab : a ≠ b) (hpar : ∀ x, Even (G.degree x) ↔ x ≠ a ∧ x ≠ b) :
    ∃ p : G.Walk a b, p.IsEulerian :=
  exists_isEulerian_trail_of_two_odd h.edgesInOneComponent hab hpar

/-!
*Euler's theorem*, full characterization: a finite graph with at least one vertex has
an Eulerian trail *iff* all its edges lie in one component and it has either no
odd-degree vertex or exactly two. The forward direction is
`IsEulerian.edgesInOneComponent` with Mathlib's `IsEulerian.card_odd_degree`; the
reverse direction is `exists_isEulerian_circuit` (no odd-degree vertex) or
`exists_isEulerian_trail_of_two_odd` (exactly two). We only reason about the number
of odd-degree vertices, so we count them with `Set.ncard` and `[Finite V]` suffices;
it implies the section's `[Finite G.edgeSet]` assumption, which we `omit`. Mathlib's
`IsEulerian.card_odd_degree` counts with `Fintype.card` instead, so the forward
direction converts between the two.
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
vertices `u, v` are `k`-edge-reachable if after deleting less than `k` edges from
`G` there is still a walk from `u` to `v`. Here the number of deleted edges is
measured with `Set.encard`, which is `⊤` if the set is infinite and otherwise its
cardinality as a natural number.
-/
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
[Figure: A 3-edge-connected graph with a 3-edge cut (red)](https://jt496.github.io/GraphTheoryInLean/figures/edge_connectivity.svg)

An edge is a bridge iff its endpoints are not `2`-edge-reachable. So a graph is
`2`-edge-connected iff deleting any single `e : Sym2 V` leaves it preconnected. Here
`e` need not be an edge of `G`, and deleting a non-edge doesn't change `G`, so this
includes `G` itself being preconnected.
-/
#check isBridge_iff_not_isEdgeReachable_two
#check isEdgeConnected_two
/-!
A graph is acyclic (a forest) iff no two distinct vertices are `2`-edge-reachable.
-/
#check isAcyclic_iff_pairwise_not_isEdgeReachable_two

/-!
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
subtype `↑Sᶜ`, so its walks run between vertices `⟨u, hu⟩` that carry proofs that
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
this first with `encard`, so that no finiteness assumption on the neighbourhood is
needed.
-/
lemma IsVertexConnected.le_encard_neighborSet {k : ℕ} (hG : G.IsVertexConnected k)
    (v : V) : (k : ℕ∞) ≤ (G.neighborSet v).encard := by
  by_contra! hlt
  obtain ⟨u, hu⟩ : ∃ u, u ∉ insert v (G.neighborSet v) := by
    by_contra! h
    -- `h` says that every vertex is `v` or a neighbour of `v`, so `G` would have at
    -- most `k` vertices
    have hle : (k + 1 : ℕ∞) ≤ k :=
      calc (k + 1 : ℕ∞) ≤ ENat.card V := hG.1
        _ = (Set.univ : Set V).encard := (Set.encard_univ V).symm
        _ ≤ (insert v (G.neighborSet v)).encard :=
            Set.encard_le_encard fun x _ => h x
        _ ≤ (G.neighborSet v).encard + 1 := Set.encard_insert_le _ _
        _ ≤ k := Order.add_one_le_of_lt hlt
    norm_cast at hle
    grind
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
Taking the box product with `K₂` raises the vertex connectivity by at least one: if
`G` is connected and `k`-vertex-connected then `G □ K₂` is
`(k + 1)`-vertex-connected. Since `Q[n + 1]` is `Q[n] □ K₂`, induction on `n` then
shows that the hypercube `Q[n]` is `n`-vertex-connected. Exercises 14–16 guide you
through the proof, and Exercise 17 uses the next section to deduce that `Q[n]` is
also `n`-edge-connected.

## Vertex Connectivity Implies Edge Connectivity

Any `k`-vertex-connected graph is also `k`-edge-connected.

Proof sketch: given a set `s` of less than `k` edges and vertices `u` and `v`, let
`s₀ ⊆ s` be those that are edges of `G`, since deleting the other elements of `s`
changes nothing. We then pick from each edge of `s₀` other than `s(u, v)` an endpoint
that is neither `u` nor `v`, and let `T` be the set of chosen endpoints
(`Finset.exists_cover_avoiding`). A walk that avoids a set of vertices meeting every
edge of `s₀` survives the deletion of `s` (`Walk.reachable_deleteEdges_of_avoids`).
If `s(u, v) ∉ s₀` then `T` meets every edge of `s₀`, and a walk from `u` to `v`
avoiding `T` exists by `k`-vertex-connectivity. Otherwise `T` has at most `k - 2`
vertices, so there is a vertex `w` outside `T ∪ {u, v}`, and we walk from `u` to `w`
avoiding `T ∪ {v}` and then from `w` to `v` avoiding `T ∪ {u}`; both of these sets
meet every edge of `s₀`, including `u — v`.

Our first lemma says that given a finite set `s` of pairs `s(a, b)` with `a ≠ b`,
there is a set `T` of vertices other than `u` and `v`, with at most one vertex for
each element of `s` other than `s(u, v)`, that meets every element of `s` other than
`s(u, v)`.
-/
lemma _root_.Finset.exists_cover_avoiding [DecidableEq V] (u v : V)
    (s : Finset (Sym2 V)) (hs : ∀ e ∈ s, ¬ e.IsDiag) :
    ∃ T : Finset V, T.card ≤ (s.erase s(u, v)).card ∧ u ∉ T ∧ v ∉ T ∧
      ∀ e ∈ s, e ≠ s(u, v) → ∃ x ∈ e, x ∈ T := by
  -- We use `choose!` below which needs `V` to be nonempty.
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
  -- Plain `choose` would give `g : (e : Sym2 V) → e ∈ s.erase s(u, v) → V`, whose
  -- second argument is a proof of membership, so `(s.erase s(u, v)).image g` would
  -- not type-check.
  -- Using `choose!` removes this proof argument, giving `g : Sym2 V → V`
  -- and `hg : ∀ e ∈ s.erase s(u, v), g e ∈ e ∧ g e ≠ u ∧ g e ≠ v`. The values of `g`
  -- outside `s.erase s(u, v)` are arbitrary, so `choose!` needs `Nonempty V`.
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
  obtain ⟨T, hTcard, hTu, hTv, hT⟩ := s₀.exists_cover_avoiding u v
    fun e he => G.not_isDiag_of_mem_edgeSet (hmem.mp he).2
  -- a set containing `T` meets every edge of `s₀`, except possibly `s(u, v)`
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
  · -- the edge `u — v` is deleted, so `#T ≤ k - 2`
    -- we need to find another vertex `w` outside `T ∪ {u, v}`
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
    -- we can walk from `u` to `w` avoiding `T ∪ {v}`
    obtain ⟨p₁, hp₁⟩ := hG.exists_walk (insert v T) (by have := hins v; grind) u w
      (by simp [hne, hTu]) (by simp [hwv, hwT])
    -- we can walk from `w` to `v` avoiding `T ∪ {u}`
    obtain ⟨p₂, hp₂⟩ := hG.exists_walk (insert u T) (by have := hins u; grind) w v
      (by simp [hwu, hwT]) (by simp [hne.symm, hTv])
    exact (p₁.reachable_deleteEdges_of_avoids (hcover _ (Finset.subset_insert _ _)
        fun _ => .inr (Finset.mem_insert_self _ _)) hp₁).trans
      (p₂.reachable_deleteEdges_of_avoids (hcover _ (Finset.subset_insert _ _)
        fun _ => .inl (Finset.mem_insert_self _ _)) hp₂)
  · -- otherwise `T` meets every edge of `s₀`
    have := Finset.card_erase_le (s := s₀) (a := s(u, v))
    obtain ⟨p, hp⟩ := hG.exists_walk T (by grind) u v hTu hTv
    exact p.reachable_deleteEdges_of_avoids (hcover T subset_rfl (absurd · huv)) hp

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
the vertex connectivity.
-/
@[inherit_doc edgeConnectivity] scoped notation "λ(" G ")" =>
  SimpleGraph.edgeConnectivity G
@[inherit_doc vertexConnectivity] scoped notation "κ(" G ")" =>
  SimpleGraph.vertexConnectivity G

/-!
Both properties are closed under decreasing `k`, so the `k` for which `G` is
`k`-edge-connected form an initial segment of `ℕ`, and `k ≤ λ(G)` holds exactly when
`G` is `k`-edge-connected. The same holds for `κ(G)` if `V` is nonempty (the graph
with no vertices is not even `0`-vertex-connected, yet `0 ≤ κ(G)`). The general fact
is about an `Antitone` property `P` of natural numbers, that is, one closed under
decreasing `k`: the supremum `⨆ (j) (_ : P j), j` in `ℕ∞` exceeds `k` iff `P (k + 1)`
holds. It says nothing about graphs, so we put it in the `ENat` namespace. Mathlib
does not currently seem to have it.
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
`edgeConnectivity_le_degree` at a vertex of minimum degree (Exercise 18). Both
inequalities can be strict (Exercises 19 and 20). In the *bowtie*, two triangles
sharing a vertex, deleting the shared vertex disconnects the graph, so `κ = 1`, while
`λ = δ = 2`. Two copies of `K[4]` joined by a single edge (the *barbell*) have
`λ = 1`, since that edge is a bridge, while `δ = 3`.

[Figure: Left: the bowtie, with $\kappa = 1 < \lambda = 2$. Right: the barbell, with $\lambda = 1 < \delta = 3$](https://jt496.github.io/GraphTheoryInLean/figures/whitney_strict.svg)

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

The greedy bound `colorable_of_degree_le` says that a graph of maximum degree at most
`Δ` is `(Δ + 1)`-colourable. *Brooks' theorem* says exactly when this can be improved
to `Δ`: a finite connected graph of maximum degree `Δ` is `Δ`-colourable unless it is
the complete graph `K[Δ + 1]` or (when `Δ = 2`) an odd cycle. Applying this to each
component, a finite graph of maximum degree at most `Δ` is `Δ`-colourable unless it
contains a `(Δ + 1)`-clique or (when `Δ = 2`) one of its components is an odd cycle.
Odd cycles are only an obstruction when `Δ = 2`: for example the Petersen graph is
`3`-regular and contains `5`-cycles, but it is `3`-colourable.

The cases `Δ = 2` and `Δ ≥ 3` are very different. The case `Δ = 2` follows quickly
from our characterization of bipartite graphs, `isBipartite_iff_forall_isCycle_even`,
while the case `Δ ≥ 3` needs a real argument, for which we use the partial colourings
of
[Partial Colourings*](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-partial-colourings).
At the end we combine the cases into a single statement for every `Δ`.

## Maximum Degree Two

The case `Δ = 2` combines two earlier results. A graph is `2`-colourable iff it has
no odd cycle (`isBipartite_iff_forall_isCycle_even`), and in a graph of maximum
degree at most `2` every cycle is a whole connected component
(`Walk.IsCycle.toSubgraph_eq_of_degree_le_two`). So a graph of maximum
degree at most `2` is `2`-colourable unless one of its connected components is an odd
cycle. Indeed, if it is not `2`-colourable then it has an odd cycle `c`, based at `u`
say, and by
`Walk.IsCycle.toSubgraph_eq_of_degree_le_two` that cycle *is* its component:
`c.toSubgraph = G⟦u⟧.toSubgraph`. This equation is how we state that a component is
an odd cycle.
-/
/-- *Brooks' theorem (Δ = 2)*: a graph with all degrees at most `2` is `2`-colourable
unless it has a component that is an odd cycle. -/
theorem brooks_two [G.LocallyFinite] (hdeg : ∀ v, G.degree v ≤ 2)
    (hcyc : ¬ ∃ (u : V) (c : G.Walk u u),
      c.IsCycle ∧ Odd c.length ∧ c.toSubgraph = G⟦u⟧.toSubgraph) :
    G.Colorable 2 := by
  apply isBipartite_iff_forall_isCycle_even.mpr
  intro u c hc
  by_contra hodd
  exact hcyc ⟨u, c, hc, Nat.not_even_iff_odd.mp hodd,
    hc.toSubgraph_eq_of_degree_le_two hdeg⟩

/-!
## Maximum Degree at Least Three

From now on we assume that `Δ ≥ 3`. The classical greedy colouring proof due to
Lovász (1975) uses the *blocks* of a graph, its maximal connected subgraphs without a
cut vertex, which we study in the next section,
[Cut Vertices and Blocks*](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-cut-vertices-and-blocks).
Instead, the proof we give is a variation of Lovász's approach that avoids blocks: it
uses partial colourings and the idea behind greedy colouring, but replaces the need
for `2`-connected blocks with strong induction on vertex subsets and a gluing step
across a pair of non-adjacent vertices.

The basic idea is to colour vertices greedily but in an order chosen so that we never
reach an uncoloured vertex with `Δ` distinctly coloured neighbours, hence the greedy
colouring will never use more than `Δ` colours.

*Proof sketch*: we prove the stronger statement that *every* finite subset of the
vertices `s : Finset V` satisfies `G.ColorableOn Δ ↑s` (`colorableOn_of_cliqueFree`),
by strong induction on `s` under `⊂`, so our induction hypothesis is:

  `ih : ∀ t ⊂ s, G.ColorableOn Δ ↑t`.

*Degeneracy reduction:* if some `a ∈ s` has less than `Δ` neighbours in `s`, then
apply `ih` to `s.erase a` and extend the resulting colouring to `a` using a free
colour (the neighbours of `a` use less than `Δ` colours;
`ColoringOn.exists_free_color_of_degIn`).

So wlog every vertex of `s` has at least `Δ` neighbours in `s`. Since all degrees are
at most `Δ`, every vertex of `s` must have *exactly* `Δ` neighbours, all of which lie
in `s` (so `s` is *closed under adjacency*: every neighbour of a vertex of `s` lies
in `s`).

*Regular case* (`regular_case`, `closed_regular_case`): write `K := s`, which is
closed under adjacency and `Δ`-regular, and pick any `v₂ ∈ K`.

Since `G` has no `(Δ + 1)`-clique, the neighbourhood of `v₂` is not a clique, so `v₂`
has two neighbours `v₁` and `v₃` that are not adjacent to each other
(`CliqueFree.exists_ne_adj_not_adj_of_le_degree`). Write `W := K \ {v₁, v₃}` for the
remaining vertices of `K`. Let `A` be the vertex set of the connected component of
`v₂` in the subgraph induced by `W` (the vertices of `W` that can be reached from
`v₂` by a walk inside `W`, `walkComponent`), and let `B := W \ A` be the rest, so
there are no edges between `A` and `B` (`adj_mem_walkComponent`). (If the pair
`{v₁, v₃}` does not *separate* `K` then `B` is empty, but we do not need to treat
this case separately.)

Now `D := A ∪ {v₁, v₃}` and `E := B ∪ {v₁, v₃}` together cover `K` and meet only in
the non-adjacent pair `{v₁, v₃}`; moreover `A`, `B` and `E` are proper subsets of
`K` (the first misses `v₁`, the others `v₂`), so `ih` applies to them. The plan is to
colour `D` and `E` separately and then glue them together using our
`ColoringOn.union` construction.

[Figure: Left: the sets $A$, $B$, $D$ and $E$ when $\Delta = 3$. Right: Step 1 on $D$, with the colouring order numbered and the search from $v_2$ in blue](https://jt496.github.io/GraphTheoryInLean/figures/brooks_split.svg)

1. *`D` has a colouring in which `v₁` and `v₃` have the same colour.*
   (`exists_coloring_eq`)

   Colour `v₁` and `v₃` first, both with colour `0` (legal, since they are not
   adjacent). Then colour the vertices of `A` other than `v₂` greedily, in
   *reverse search order from `v₂`*. That is, start with `S = {v₂}` and repeatedly
   add to `S` a vertex of `A` outside `S` that has a neighbour in `S`; we say such a
   vertex has been *settled*. Since `A` is connected
   (`induce_walkComponent_connected`), every vertex of `A` is eventually settled
   (`exists_adj_sdiff_of_connected`). Now colour the vertices in the reverse of the
   order in which they were settled (`exists_coloringOn_sdiff`). Each vertex was
   settled because of an edge to an already-settled neighbour, which is either
   `v₂` or a vertex coloured later; so when a vertex is coloured it still has an
   uncoloured neighbour, hence at most `Δ - 1` coloured neighbours, and a free colour
   exists.

   Finally colour `v₂`: among its `Δ` neighbours are `v₁` and `v₃`, which received
   the *same* colour, so its neighbours use at most `Δ - 1` colours and a free colour
   remains (`exists_coloringOn_insert_of_eq`).

2. *Gluing.* Since the only edges from `D` to `E \ D ⊆ B` leave from `{v₁, v₃}`
   (there are no `A`–`B` edges), two colourings of `D` and `E` can be glued together
   as long as they agree on `{v₁, v₃}`. Moreover they can be made to agree by
   permuting the colours of one of them (`Equiv.exists_perm_of_eq_iff_eq`), provided
   that they agree on *whether* `v₁` and `v₃` receive equal colours. So it suffices
   (`ColoringOn.nonempty_union_of_eq_iff_eq`) to find colourings of `D` and `E` with
   the same *pattern* (equal or distinct) on `{v₁, v₃}`
   (`exists_colorings_pattern_iff`).

   By Step 1, `D` has a colouring with `v₁` and `v₃` *equal*. Also, for
   `v ∈ {v₁, v₃}` the `Δ` neighbours of `v` split between `A` and `B`, with at least
   one (namely `v₂`) in `A`.

   *Case (a).* If `v₁` and `v₃` have at most `Δ - 1` neighbours in `B` *in total* (as
   happens when `B` is empty), colour `B` by `ih` and extend to `E` giving `v₁, v₃` a
   common free colour (`exists_two_eq`); pair this with the equal-pattern colouring
   of `D`.

   *Case (b).* Otherwise one of `v₁, v₃`, say `v₁`, has at least `2` neighbours in
   `B` and hence at most `Δ - 2` in `A`. The other, `v₃`, has at most `Δ - 1`
   neighbours in `A`: since `v₂ ∈ A`, `v₁` has at most `Δ - 1` neighbours in `B`, so
   `v₃` has at least one there. So a colouring of `A` by `ih` extends to `D` giving
   `v₁, v₃` *distinct* colours (`exists_two_ne`). So `D` has colourings of both
   patterns, and we pair the `ih`-colouring of `E` with whichever one matches it.
-/
section brooks
open Finset
variable {Δ : ℕ}

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
private lemma ColoringOn.exists_free_color [DecidableRel G.Adj] {s : Finset V}
    (C : G.ColoringOn (Fin Δ) ↑s) (a : V)
    (h : #({v ∈ s | G.Adj a v}.image fun v => C v) < Δ) :
    ∃ c : Fin Δ, ∀ v ∈ s, G.Adj a v → C v ≠ c := by
  obtain ⟨c, hc⟩ := exists_color_avoiding _ h
  exact ⟨c, fun v hv hadj heq =>
    hc (mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hadj⟩, heq⟩)⟩

/-!
We count the neighbours of `a` lying in a finite set `s` with `G.degIn s a` (see
`degIn`). Combining `exists_free_color` with `card_image_le`: if `a` has less than
`Δ` neighbours in `s`, then the number of colours used on those neighbours is less
than `Δ`, so some colour is free for `a`.
-/
lemma ColoringOn.exists_free_color_of_degIn [DecidableRel G.Adj]
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

If the subgraph induced by `W` is connected, and `S ⊂ W` is a set of settled
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
    -- every vertex of `W` is settled: colour just `v₁` and `v₃`, both with
    -- colour `0`
    intro S _ _ hcard
    have hWS : W \ S = ∅ := card_eq_zero.mp hcard
    exact ⟨(G.coloringOnOfNotAdj hnadj ⟨0, hΔ⟩).copy (by simp [hWS]), rfl⟩
  | succ n ih =>
    intro S hv hS hcard
    have hWS : (W \ S).Nonempty := card_pos.mp (by grind)
    -- settle an unsettled vertex `z` with a settled neighbour `y`; colour the rest
    -- by induction, then give `z` a free colour
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
    grind [ColoringOn.copy_apply, ColoringOn.insert_apply]

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

Case (a) of Step 2. Extend a colouring of `B` by two new non-adjacent vertices `x, y`
giving them the *same* colour, when their numbers of neighbours in `B` sum to less
than `Δ`, so that together they see less than `Δ` colours.
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
  -- `x` is not adjacent to `y`, so it sees the same colours on `insert y A` as
  -- on `A`
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
    by simp_all [Ne.symm]⟩


/-!
The sketch uses the set `A`: the vertices of `W := K \ {v₁, v₃}` reachable from `v₂`
by a walk inside `W`, i.e. the vertex set of the component of `v₂` in the subgraph
induced by `W`. We define this, as a `Finset`, for any finite set `W` and record what
we need: it contains `v₂` (when `v₂ ∈ W`; `self_mem_walkComponent`), it is closed
under adjacency into `W` (`adj_mem_walkComponent`), and the subgraph it induces is
connected (`induce_walkComponent_connected`).
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
Extending a walk inside `W` from `v₂` to `a` by an edge `a — b` with `b ∈ W` shows
that `walkComponent` is closed under adjacency into `W`.
-/
lemma adj_mem_walkComponent {W : Finset V} {v₂ a b : V}
    (ha : a ∈ G.walkComponent v₂ W) (hb : b ∈ W) (hab : G.Adj a b) :
    b ∈ G.walkComponent v₂ W := by
  obtain ⟨-, p, hp⟩ := mem_walkComponent.mp ha
  refine mem_walkComponent.mpr ⟨hb, p.concat hab, fun y hy => ?_⟩
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
  grind

/-!
Truncating a walk inside `W` from `v₂` to `a` at its first visit to a vertex `y` on
it shows that `y` lies in `walkComponent` too, so the whole walk does.
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
Combined with `ColoringOn.union`, this gives the gluing step. Suppose that `A` and
`B` meet only in `{x, y}`, and that there are no edges between `A \ B` and `B \ A`.
Then colourings `C` of `A` and `D` of `B` with the same pattern on `{x, y}` can be
glued into a colouring of `A ∪ B`: permute the colours of `D` so that it agrees with
`C` on `{x, y}`, and use `C` on `A` and the permuted `D` on `B \ A`.
-/
lemma ColoringOn.nonempty_union_of_eq_iff_eq {α : Type*} {A B : Set V} {x y : V}
    (C : G.ColoringOn α A) (D : G.ColoringOn α B) (hmeet : A ∩ B ⊆ {x, y})
    (hcross : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v)
    (hpat : C x = C y ↔ D x = D y) : Nonempty (G.ColoringOn α (A ∪ B)) := by
  classical
  obtain ⟨σ, hσx, hσy⟩ := Equiv.exists_perm_of_eq_iff_eq hpat
  refine ⟨C.union (D.map σ.toEmbedding) fun u v hu hv huv => ?_⟩
  by_cases hu' : u ∈ B
  · -- `u` is `x` or `y`, where `C` agrees with the permuted `D`
    have hσu : σ (D u) = C u := by
      obtain rfl | rfl : u = x ∨ u = y := by simpa using hmeet ⟨hu, hu'⟩
      exacts [hσx, hσy]
    rw [ColoringOn.map_apply, ← hσu]
    exact fun h => D.valid ⟨hu', hv.1, huv⟩ (σ.injective h)
  · -- otherwise `u ∈ A \ B` and `v ∈ B \ A`, which are not adjacent
    exact absurd huv (hcross u ⟨hu, hu'⟩ v hv)

/-!
Step 2 of the sketch: colourings of `D := A ∪ {v₁, v₃}` and `E := B ∪ {v₁, v₃}` with
the same pattern (equal or distinct) on `{v₁, v₃}`. Here `A` is given abstractly,
with the properties of the walk-component that we need as hypotheses, and
`B := K \ (A ∪ {v₁, v₃})`. Cases (a) and (b) of Step 2 are the two branches of the
`by_cases` on the number of neighbours of `v₁` and `v₃` in `B`.
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
  -- `A` and `B` partition `K \ {v₁, v₃}`
  have hABdisj : Disjoint A B := Finset.disjoint_left.mpr
    (fun z hzA hzB => (mem_sdiff.mp hzB).2 (mem_union_left _ hzA))
  have hABcov : A ∪ B = K \ {v₁, v₃} := by grind
  -- the `Δ` neighbours of `v₁` (resp. `v₃`) split between `A` and `B`,
  -- with `v₂` in `A`
  have hNsub : ∀ v ∈ ({v₁, v₃} : Finset V), G.neighborFinset v ⊆ K \ {v₁, v₃} := by
    grind [mem_neighborFinset, adj_symm]
  have hNK : ∀ v ∈ ({v₁, v₃} : Finset V), G.degIn A v + G.degIn B v = Δ := by
    intro v hv
    rw [← degIn_union A B v hABdisj, hABcov, degIn_eq_degree (hNsub v hv),
      hregK v (h13K hv)]
  have hAv1 := hNK v₁ (by grind)
  have hAv3 := hNK v₃ (by grind)
  have hA1pos : 1 ≤ G.degIn A v₁ :=
    card_pos.mpr ⟨v₂, mem_filter.mpr ⟨hv₂A, ha1.symm⟩⟩
  have hA3pos : 1 ≤ G.degIn A v₃ :=
    card_pos.mpr ⟨v₂, mem_filter.mpr ⟨hv₂A, ha3.symm⟩⟩
  -- the neighbours of `v₂` are in `D`, since `A` is closed
  -- under adjacency into `K \ {v₁, v₃}`
  have hnbhdD : G.neighborFinset v₂ ⊆ (A ∪ {v₁, v₃}).erase v₂ := by
    intro w hw
    grind [(mem_neighborFinset _ _ _).mp hw]
  have hMA : (A ∪ {v₁, v₃}) \ {v₁, v₃} = A := by grind
  -- `D` always has a colouring with `v₁, v₃` the same colour (Step 1 applied to `D`)
  obtain ⟨C_D_eq, hC_D_eq⟩ := exists_coloring_eq (A ∪ {v₁, v₃}) (by grind)
    (mem_union_left _ hv₂A) (mem_union_right _ (by simp))
    (mem_union_right _ (by simp)) hne13 hnadj hd2 ha1 ha3
    (by grind) hnbhdD (by grind)
  have hAss : A ⊂ K := (ssubset_iff_of_subset hAK).mpr ⟨v₁, hv1K, hv1A⟩
  -- `E = B ∪ {v₁, v₃}` is a proper subset of `K` (it misses `v₂ ∈ A`)
  have hv₂E : v₂ ∉ B ∪ {v₁, v₃} := by grind
  have hEss : B ∪ {v₁, v₃} ⊂ K := by grind
  -- `by_cases!` runs `by_cases` and then `push Not` in the second (negated) subgoal
  by_cases! hsum : G.degIn B v₁ + G.degIn B v₃ ≤ Δ - 1
  · -- Case (a): colour `B` by `ih` and give `v₁, v₃` a common free colour
    have hBss : B ⊂ K := (ssubset_iff_of_subset sdiff_subset).mpr
      ⟨v₂, hv₂K, fun h => hv₂E (mem_union_left _ h)⟩
    obtain ⟨C_B0⟩ := ih B hBss
    obtain ⟨C_E, hC_E⟩ := exists_two_eq B C_B0 hnadj (by grind)
    exact ⟨C_D_eq, C_E.copy (by grind), iff_of_true hC_D_eq hC_E⟩
  · -- Case (b): colour `A` by `ih` and give `v₁, v₃` distinct colours
    obtain ⟨C_A⟩ := ih A hAss
    have hDdist : ∃ C : G.ColoringOn (Fin Δ) ↑(A ∪ {v₁, v₃}), C v₁ ≠ C v₃ := by
      -- one of `v₁, v₃` has at least `2` neighbours in `B`
      -- ("say `v₁`" in the sketch)
      by_cases h2 : 2 ≤ G.degIn B v₁
      · obtain ⟨C', hC'⟩ := exists_two_ne A C_A hne13 hnadj  (by grind) (by grind)
        exact ⟨C'.copy (by grind), hC'⟩
      · obtain ⟨C', hC'⟩ :=
          exists_two_ne A C_A (Ne.symm hne13) (fun h => hnadj h.symm)
            (by grind) (by grind)
        exact ⟨C'.copy (by grind), fun h => hC' h.symm⟩
    obtain ⟨C_D_dist, hC_D_dist⟩ := hDdist
    obtain ⟨C_E⟩ := ih _ hEss
    -- pair the `ih`-colouring of `E` with the colouring of `D` of the same pattern
    by_cases hEpat : C_E v₁ = C_E v₃
    · exact ⟨C_D_eq, C_E, iff_of_true hC_D_eq hEpat⟩
    · exact ⟨C_D_dist, C_E, iff_of_false hC_D_dist hEpat⟩

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
  -- `D ∪ E = K`
  have hDEK : (A ∪ {v₁, v₃}) ∪ (B ∪ {v₁, v₃}) = K := by grind
  -- `D` and `E` meet in `{v₁, v₃}`, and there are no edges between `A` and `B`, so
  -- the two colourings can be glued
  obtain ⟨C⟩ := C_D.nonempty_union_of_eq_iff_eq C_E₀ (by grind)
    (fun u hu w hw huw => by grind) hpat
  exact ⟨C.copy (by rw [← coe_union, hDEK])⟩

/-!
The regular case of the sketch: every vertex of `s` has degree `Δ` and all its
neighbours in `s`, so `closed_regular_case` colours `s` (taking `K = s`).
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
  exact closed_regular_case hΔ hcf s v₂ hv₂ hsubs hdegs ih

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
  · -- `s = ∅`: `coloringOnEmpty` needs a colour; `Fin Δ` is nonempty since `0 < Δ`
    exact ⟨(G.coloringOnEmpty ⟨0, by grind⟩).copy (by simp)⟩
  by_cases! hex : ∃ a ∈ s, G.degIn s a < Δ
  · -- Degeneracy reduction: erase a low-degree vertex and extend greedily
    obtain ⟨a, ha, hlt⟩ := hex
    obtain ⟨C⟩ := ih _ (erase_ssubset ha)
    have hlt' : G.degIn (s.erase a) a < Δ :=
      (degIn_mono (erase_subset a s) a).trans_lt hlt
    obtain ⟨c, hc⟩ := C.exists_free_color_of_degIn a hlt'
    exact ⟨(C.insert a (fun v hv hadj => hc v hv hadj)).copy (by simp_all)⟩
  · -- Regular case: every vertex of `s` has all `Δ` of its neighbours inside `s`
    exact regular_case hΔ hcf hdeg s hne hex ih

/-!
Brooks' theorem (for finite graphs with `Δ ≥ 3`): a finite graph that is
`(Δ + 1)`-clique-free with maximum degree at most `Δ ≥ 3` is `Δ`-colourable.
-/
theorem brooks [G.LocallyFinite] [Finite V] (hΔ : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1))
    (hdeg : ∀ v, G.degree v ≤ Δ) : G.Colorable Δ := by
  have := Fintype.ofFinite V
  exact (colorableOn_univ_iff_colorable G Δ).1
    (by simpa using colorableOn_of_cliqueFree hΔ hcf hdeg univ)

end brooks
/-!
By De Bruijn–Erdős, Brooks' theorem extends to infinite graphs.
-/
/-- *Brooks' theorem (Δ ≥ 3)*: a locally finite graph that is `(Δ + 1)`-clique-free
with maximum degree at most `Δ ≥ 3` is `Δ`-colourable. -/
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
## Brooks' Theorem Full Version

We can now put the cases together. When `Δ ≤ 1` there is nothing to prove: a graph
with no `1`-clique has no vertices, and a graph with no `2`-clique has no edges
(`cliqueFree_one` and `cliqueFree_two`).
-/
/-- *Brooks' theorem*: a graph with all degrees at most `Δ` and no `(Δ + 1)`-clique
is `Δ`-colourable, unless `Δ = 2` and one of its components is an odd cycle. -/
theorem brooks_general [G.LocallyFinite] {Δ : ℕ}
    (hdeg : ∀ v, G.degree v ≤ Δ) (hcf : G.CliqueFree (Δ + 1))
    (hcyc : Δ = 2 → ¬ ∃ (u : V) (c : G.Walk u u),
      c.IsCycle ∧ Odd c.length ∧ c.toSubgraph = G⟦u⟧.toSubgraph) :
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
fails for graphs with infinitely many components.)

A *block* of a graph `G` is a subgraph `B` that is connected and has no cut vertex of
its own, and that is maximal among such subgraphs: no larger subgraph of `G` is both
connected and free of cut vertices. So every block is of one of three kinds: a
maximal `2`-connected subgraph, a bridge (the subgraph consisting of just that edge
and its two endpoints), or an isolated vertex. One reason for caring about blocks is
that they can help with colouring a graph: for `n ≥ 1`, a graph is `n`-colourable iff
each of its blocks is. In this section we prove the harder direction for finite
graphs (`colorable_of_forall_block`); the exercises give the converse and extend the
result to all graphs (`colorable_iff_forall_block`).

A separate pedagogical motivation for introducing blocks is that it gives us a good
excuse to describe a graph-theoretic construction built from first principles using
an equivalence relation and Lean's `Quotient` type.

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
      exact hcut x ⟨u, v, by grind, by grind, hconn u v, fun p => by grind [h p]⟩

/-!
A cut vertex can lie in several blocks, so the blocks do not partition the vertices
of a graph, but they do partition its *edges*. So we define blocks in the same way as
connected components, via an equivalence relation, but on edges rather than vertices.
The relation we use is *cycle-equivalence*: two edges are equivalent if they are the
same edge or lie in a common cycle. The equivalence classes of this relation will be
the blocks of the graph. A bridge lies on no cycles, so it forms a block on its own.

Apart from isolated vertices, the blocks in the sense defined at the start of this
section are exactly the subgraphs spanned by these equivalence classes, though we
will not prove this. An isolated vertex lies in no edge, so it belongs to no block in
our sense; in particular a graph with no edges has no blocks at all. (This is why our
colouring results assume `n ≥ 1`: the graph `K[1]` has no blocks, so all its blocks
are (vacuously) `0`-colourable, but `K[1]` is not `0`-colourable.)

[Figure: A graph with four blocks, its edges coloured by block: the $4$-cycle $a, b, c, d$ with the chord $b d$ (blue), the triangle $c, e, f$ (green) and the bridges $c g$ (orange) and $f h$ (violet). The cut vertices $c$ and $f$ (red) lie in three and two blocks, and the isolated vertex $i$ lies in no block](https://jt496.github.io/GraphTheoryInLean/figures/blocks.svg)

Like the deleted sets in `IsEdgeReachable`, cycle-equivalence is most conveniently
defined on all of `Sym2 V`, not just on `G.edgeSet`. So until we restrict to
`G.edgeSet` in
[Blocks as a Quotient of Edges](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-blocks-as-a-quotient-of-edges),
*edge* means any element `s(u, v)` of `Sym2 V`, and we say *edge of `G`* for an
element of `G.edgeSet`. An edge that is not an edge of `G` lies on no cycles, so it
is cycle-equivalent only to itself.
-/
/-- *Cycle-equivalence*, a relation on `Sym2 V`: two edges are related if they are
equal or lie on a common cycle. -/
def CycleEquivalent (G : SimpleGraph V) : Sym2 V → Sym2 V → Prop :=
  fun e₁ e₂ => e₁ = e₂ ∨
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ e₁ ∈ c.edges ∧ e₂ ∈ c.edges

/-!
## Cycle-Equivalence

`CycleEquivalent` is reflexive by definition. It is also symmetric, and preserves
membership in the edge set: if `e ≠ f` are cycle-equivalent, both lie on a cycle of
`G`, so both are edges of `G`.
-/
lemma CycleEquivalent.symm {e f : Sym2 V} (h : G.CycleEquivalent e f) :
    G.CycleEquivalent f e := by
  rcases h with (rfl | ⟨u, c, hc, h1, h2⟩)
  · left; rfl
  · right; exact ⟨u, c, hc, h2, h1⟩

lemma CycleEquivalent.mem_edgeSet_iff {e f : Sym2 V} (h : G.CycleEquivalent e f) :
    e ∈ G.edgeSet ↔ f ∈ G.edgeSet := by
  rcases h with rfl | ⟨_, p, _, he, hf⟩
  · rfl
  · exact iff_of_true (p.edges_subset_edgeSet he) (p.edges_subset_edgeSet hf)

/-!
`CycleEquivalent` is in fact also transitive: two cycles sharing an edge `f`, one
containing the edge `e` and the other containing the edge `g`, can be spliced into a
single cycle through `e` and `g`. Proving this in Lean would be painful (but not
impossible); however, we can avoid it. Mathlib allows us to form the equivalence
relation *generated* by any relation.
-/
#source Relation.EqvGen

/-!
Using this we can define *block-equivalence* of edges to be the equivalence relation
generated by `CycleEquivalent`, which is an equivalence relation by construction.
-/
/-- Two edges are *block-equivalent* if they are related by the equivalence relation
generated by `CycleEquivalent`. -/
def BlockEquivalent (G : SimpleGraph V) : Sym2 V → Sym2 V → Prop :=
  Relation.EqvGen G.CycleEquivalent

/-!
`BlockEquivalent` is an equivalence relation (by construction).
-/
lemma blockEquivalent_equivalence : Equivalence G.BlockEquivalent :=
  Relation.EqvGen.is_equivalence _

lemma BlockEquivalent.refl (e : Sym2 V) : G.BlockEquivalent e e :=
  G.blockEquivalent_equivalence.refl e

lemma BlockEquivalent.symm {e f : Sym2 V} (h : G.BlockEquivalent e f) :
    G.BlockEquivalent f e :=
  G.blockEquivalent_equivalence.symm h

lemma BlockEquivalent.trans {e f g : Sym2 V} (h₁ : G.BlockEquivalent e f)
    (h₂ : G.BlockEquivalent f g) : G.BlockEquivalent e g :=
  G.blockEquivalent_equivalence.trans h₁ h₂

/-!
Cycle-equivalent edges are block-equivalent.
-/
lemma CycleEquivalent.blockEquivalent {e f : Sym2 V} (h : G.CycleEquivalent e f) :
    G.BlockEquivalent e f := Relation.EqvGen.rel _ _ h

/-!
So block-equivalence also preserves membership in the edge set. Notice that we use
induction on `h : G.BlockEquivalent e f` in the proof.
-/
lemma BlockEquivalent.mem_edgeSet_iff {e f : Sym2 V} (h : G.BlockEquivalent e f) :
    e ∈ G.edgeSet ↔ f ∈ G.edgeSet := by
  induction h with
  | rel x y hxy => exact hxy.mem_edgeSet_iff
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-!
## Blocks as a Quotient of Edges

Just as `ConnectedComponent` is the quotient of `V` by `Reachable`, a *block* is an
equivalence class of edges under `BlockEquivalent`, packaged as a quotient of
`G.edgeSet`. (Mathlib defines `ConnectedComponent` as `Quot G.Reachable`: a setoid on
`V` cannot be an instance, since `Setoid V` does not mention `G`. Our setoid lives on
`G.edgeSet`, so it can be an instance, and we use `Quotient`. The two are
interchangeable, since `Quotient s` is by definition `Quot s.r`.)

The setoid is built in two steps. First, `Relation.EqvGen.setoid G.CycleEquivalent`
bundles block-equivalence (the equivalence relation generated by `CycleEquivalent`)
as a setoid on all of `Sym2 V`. But `Sym2 V` also contains pairs that are not edges
of `G`, and we only want classes of edges. So we pull the setoid back along the
inclusion `Subtype.val : G.edgeSet → Sym2 V` using `Setoid.comap`, which relates two
edges exactly when their underlying elements of `Sym2 V` are related. We make the
result an instance, so that we can write `e ≈ f` for block-equivalent edges. From now
on, *edge* means an edge of `G`.
-/
/-- The setoid on the edges of `G` given by block-equivalence (analogue of Mathlib's
`G.reachableSetoid`). -/
instance blockSetoid (G : SimpleGraph V) : Setoid G.edgeSet :=
  Setoid.comap Subtype.val (Relation.EqvGen.setoid G.CycleEquivalent)

/-!
Unfolding the definitions, two edges are related by `blockSetoid` exactly when they
are block-equivalent.
-/
example (e f : G.edgeSet) : e ≈ f ↔ G.BlockEquivalent e f := Iff.rfl

/-- A *block* of `G` is a block-equivalence class of edges of `G` (analogue of
`ConnectedComponent`). -/
def Block (G : SimpleGraph V) := Quotient G.blockSetoid

/-- The block containing a given edge of `G`. -/
def blockMk (G : SimpleGraph V) (e : G.edgeSet) : G.Block := Quotient.mk'' e

/-!
For an edge given by an adjacency proof `h : G.Adj u v` we write `h.block` for its
block.
-/
/-- The block containing the edge `u — v`. -/
abbrev Adj.block {u v : V} (h : G.Adj u v) : G.Block := G.blockMk ⟨s(u, v), h⟩

/-!
Reversing an edge does not change its block.
-/
lemma Adj.block_symm {u v : V} (h : G.Adj u v) : h.symm.block = h.block := by
  simp only [Adj.block, Sym2.eq_swap]

/-!
Two edges lie in the same block exactly when they are block-equivalent.
-/
lemma blockMk_eq_blockMk_iff {e f : G.edgeSet} :
    G.blockMk e = G.blockMk f ↔ e ≈ f :=
  Quotient.eq''

/-!
Mathlib makes a connected component `C` into a subgraph by taking its vertices
`C.supp` (the vertices whose class is `C`) and forming the induced subgraph
`(⊤ : G.Subgraph).induce C.supp`. We could do the same here, inducing on the
endpoints of the edges in a block `B`. For components this is fine, since any edge
between two vertices of a component clearly lies in that component. For blocks the
corresponding fact, that an edge of `G` joining two vertices of a block belongs to
the block, is also true (adding such an edge to a `2`-connected subgraph keeps it
`2`-connected), but proving it needs a cycle-splicing argument like the one we
avoided above. Without it, the edges of the induced subgraph would not provably be
the edges of `B`. So instead we define the subgraph underlying a block `B` via the
edges of `G` whose class is `B`, together with their endpoints.
-/
/-- The subgraph of `G` underlying a block `B`: the edges of `G` whose block is `B`,
and their endpoints (analogue of `ConnectedComponent.toSubgraph`). -/
def Block.toSubgraph (B : G.Block) : G.Subgraph where
  verts := {v | ∃ e : G.edgeSet, v ∈ (e : Sym2 V) ∧ G.blockMk e = B}
  Adj v w := ∃ h : G.Adj v w, h.block = B
  adj_sub := fun ⟨h, _⟩ => h
  edge_vert := fun ⟨h, hB⟩ => ⟨⟨_, h⟩, Sym2.mem_mk_left _ _, hB⟩
  symm := ⟨fun _ _ ⟨h, hB⟩ => ⟨h.symm, h.block_symm.trans hB⟩⟩

@[simp] lemma Block.toSubgraph_adj {B : G.Block} {v w : V} :
    B.toSubgraph.Adj v w ↔ ∃ h : G.Adj v w, h.block = B :=
  Iff.rfl

@[simp] lemma Block.mem_toSubgraph_verts {B : G.Block} {v : V} :
    v ∈ B.toSubgraph.verts ↔ ∃ e : G.edgeSet, v ∈ (e : Sym2 V) ∧ G.blockMk e = B :=
  Iff.rfl

/-!
In the block of an edge `e`, two vertices are adjacent exactly when they are joined
by an edge of `G` that is block-equivalent to `e`.
-/
lemma blockMk_toSubgraph_adj {e : G.edgeSet} {v w : V} :
    (G.blockMk e).toSubgraph.Adj v w ↔ G.Adj v w ∧ G.BlockEquivalent e s(v, w) :=
  ⟨fun ⟨h, hB⟩ => ⟨h, (blockMk_eq_blockMk_iff.mp hB).symm⟩,
    fun ⟨h, he⟩ => ⟨h, blockMk_eq_blockMk_iff.mpr he.symm⟩⟩

/-!
Blocks behave well under taking supergraphs and, more generally, under copies
`f : Copy G H` (injective homomorphisms): these map cycles to cycles, and hence
cycle-equivalent edges to cycle-equivalent edges.
-/
lemma CycleEquivalent.map {W : Type*} {H : SimpleGraph W} (f : Copy G H)
    {a b : Sym2 V} (h : G.CycleEquivalent a b) :
    H.CycleEquivalent (a.map f) (b.map f) := by
  rcases h with rfl | ⟨u, c, hc, ha, hb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f u, c.map f.toHom,
      (Walk.isCycle_map_iff_of_injective f.injective).mpr hc,
      by simpa using ⟨a, ha, rfl⟩, by simpa using ⟨b, hb, rfl⟩⟩

/-!
Block-equivalence is preserved by copies.
-/
lemma BlockEquivalent.map {W : Type*} {H : SimpleGraph W} (f : Copy G H)
    {a b : Sym2 V} (h : G.BlockEquivalent a b) :
    H.BlockEquivalent (a.map f) (b.map f) := by
  induction h with
  | rel x y hxy => exact (hxy.map f).blockEquivalent
  | refl x => exact .refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-!
So a copy `f : Copy G H` sends the block of an edge `e` to the block of `e.map f`,
and by `BlockEquivalent.map` this does not depend on the choice of `e`. So `f`
induces a map `Block.map f : G.Block → H.Block`, just as a homomorphism induces a
map of connected components (`ConnectedComponent.map`).
-/
/-- The image of a block under a copy `f`: the block containing the images of its
edges. -/
def Block.map {W : Type*} {H : SimpleGraph W} (f : Copy G H) (B : G.Block) :
    H.Block :=
  Quotient.map' (fun e => ⟨e.1.map f, f.toHom.map_mem_edgeSet e.2⟩)
    (fun _ _ => BlockEquivalent.map f) B

/-!
Moreover, `f` maps each block `B` into the block `B.map f`: an edge `v — w` of `G`
in `B` goes to the edge `f v — f w` of `H`, which lies in `B.map f` by the
definition of `Block.map`.
-/
lemma Block.map_toSubgraph_le {W : Type*} {H : SimpleGraph W} (f : Copy G H)
    (B : G.Block) : B.toSubgraph.map f.toHom ≤ (B.map f).toSubgraph := by
  constructor
  · rintro _ ⟨v, ⟨e, hv, rfl⟩, rfl⟩
    exact ⟨⟨_, f.toHom.map_mem_edgeSet e.2⟩, Sym2.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩
  · rintro _ _ ⟨v, w, ⟨h, rfl⟩, rfl, rfl⟩
    exact ⟨f.toHom.map_adj h, rfl⟩

/-!
To pull back colourings of blocks of `H` to blocks of `G` with `Colorable.of_hom`,
we turn such an inclusion into a homomorphism between the coerced graphs. Mathlib has
the special case `Subgraph.inclusion` for `f = Hom.id`.
-/
/-- A homomorphism `f : G →g H` restricts to a homomorphism from a subgraph `A` of
`G` to any subgraph `B` of `H` containing `A.map f`. -/
def _root_.SimpleGraph.Subgraph.homOfMapLE {W : Type*} {H : SimpleGraph W}
    (f : G →g H) {A : G.Subgraph} {B : H.Subgraph} (h : A.map f ≤ B) :
    A.coe →g B.coe where
  toFun v := ⟨f v, h.1 ⟨v, v.2, rfl⟩⟩
  map_rel' hvw := h.2 ⟨_, _, hvw, rfl, rfl⟩

/-!
We also need to extend colourings in the other direction: if a subgraph `H` contains
every edge of `G`, then for `n ≥ 1` a colouring of `H` extends to `G`, giving the
vertices outside `H` colour `0`.
-/
lemma _root_.SimpleGraph.Subgraph.colorable_of_forall_adj {n : ℕ} (hn : 1 ≤ n)
    (H : G.Subgraph) (hH : ∀ ⦃v w⦄, G.Adj v w → H.Adj v w) (hc : H.coe.Colorable n) :
    G.Colorable n := by
  classical
  obtain ⟨C⟩ := hc
  refine ⟨Coloring.mk (fun v => if h : v ∈ H.verts then C ⟨v, h⟩ else ⟨0, hn⟩)
    fun {v w} hvw => ?_⟩
  have h := hH hvw
  simpa [H.edge_vert h, H.edge_vert h.symm] using
    C.valid (by simpa : H.coe.Adj ⟨v, _⟩ ⟨w, _⟩)

/-!
## Colouring a Graph from its Blocks

We now prove `colorable_of_forall_block`: for `n ≥ 1`, a finite graph is
`n`-colourable if each of its blocks is. The idea is to cut `G` into two pieces that
share at most one vertex, colour each piece, and glue the colourings using
`Colorable.sup_of_subsingleton_inter`.
-/
#check Colorable.sup_of_subsingleton_inter

/-- We say that `G` *splits at* `x` if it is the union of two proper subgraphs whose
supports meet in at most `x`. -/
def SplitsAt (G : SimpleGraph V) (x : V) : Prop :=
  ∃ G₁ G₂ : SimpleGraph V, G₁ < G ∧ G₂ < G ∧ G₁ ⊔ G₂ = G ∧
    G₁.support ∩ G₂.support ⊆ {x}

/-!
Splitting at `x` is not the same as `x` being a cut vertex. A graph with a cut vertex
`x` splits at `x`, but a graph whose edges lie in two different components splits at
every vertex, whether or not it is a cut vertex. Isolated vertices also play no role
in `SplitsAt`. (For a connected graph the two notions do agree.) `SplitsAt` is what
our colouring argument needs. There are two cases: if `G` splits at some vertex, it
is glued together from two proper pieces sharing at most one vertex, which we can
colour separately; if `G` splits nowhere, all its edges lie in one block, so a
colouring of that block colours `G`. The second case would fail for cut vertices,
since a graph with no cut vertex can have one block in each of its components.

We show that a graph with a cut vertex `x` splits at `x` (`IsCutVertex.splitsAt`),
and so does a graph with edges in two different connected components, at any vertex
(`splitsAt_of_not_reachable`). Both follow from a single lemma about walks. Fix a
non-isolated vertex `u ≠ x`, and call a vertex *near* if there is a walk from `u` to
it avoiding `x`. Let `G₁` consist of the edges of `G` with a near endpoint, and let
`G₂ = G \ G₁` (both as `SimpleGraph V`). A vertex `z ≠ x` adjacent to a near vertex
is itself near, so the supports of `G₁` and `G₂` meet in at most `x`. The edges of
`G` incident to `u` lie in `G₁`, so `G₂` is proper, and `G₁` is proper as long as
some edge of `G` has no near endpoint.
-/
lemma splitsAt_of_not_near {u x a b : V} (hux : u ≠ x) (hu : u ∈ G.support)
    (hab : G.Adj a b) (ha : ∀ p : G.Walk u a, x ∈ p.support)
    (hb : ∀ p : G.Walk u b, x ∈ p.support) : G.SplitsAt x := by
  -- `R z`: the vertex `z` is near.
  let R : V → Prop := fun z => ∃ p : G.Walk u z, x ∉ p.support
  have hR : ∀ {y z}, R y → G.Adj y z → z ≠ x → R z := by
    rintro y z ⟨p, hp⟩ hyz hzx
    exact ⟨p.concat hyz, by simp [Walk.support_concat, hp, hzx.symm]⟩
  let G₁ := G ⊓ fromRel fun y z => R y ∨ R z
  let G₂ := G \ G₁
  obtain ⟨u', hu'⟩ := hu
  have hRu : R u := ⟨.nil, by simpa using hux.symm⟩
  have hRa : ¬ R a := fun ⟨p, hp⟩ => hp (ha p)
  have hRb : ¬ R b := fun ⟨p, hp⟩ => hp (hb p)
  refine ⟨G₁, G₂, lt_of_le_not_ge inf_le_left fun h => ?_,
    lt_of_le_not_ge sdiff_le fun h => ?_, sup_sdiff_cancel_right inf_le_left, ?_⟩
  · simpa [G₁, hRa, hRb] using h hab
  · simpa [G₂, G₁, hRu, hu'.ne] using h hu'
  · rintro z ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    by_contra hzx
    simp only [sdiff_adj, inf_adj, fromRel_adj, Set.mem_ofPred_eq, G₁, G₂] at hy hy'
    have hz : ¬ R z := by grind
    have : ¬ R y := fun hRy => hz (hR hRy hy.1.symm hzx)
    grind

/-!
If `x` is a cut vertex then `G` splits at `x`. Suppose `x` separates `u` from `v`; we
apply `splitsAt_of_not_near` with near vertices taken relative to `u`. Then `u` and
`v` are distinct, so both are non-isolated. Let `y` be a neighbour of `v`. Neither
`v` nor `y` is near: every walk from `u` to `v` passes through `x`, and so does every
walk from `u` to `y`, since otherwise it would extend to a walk from `u` to `v`
avoiding `x`. So the edge `v — y` has no near endpoint, and `splitsAt_of_not_near`
applies.
-/
lemma IsCutVertex.splitsAt {x : V} (h : G.IsCutVertex x) : G.SplitsAt x := by
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
If `G` has edges in two different components then it splits at every vertex: if the
edges `a — b` and `c — d` lie in different components, then neither endpoint of
`c — d` is near (relative to `a`, provided `a ≠ x`), so `splitsAt_of_not_near`
applies; if `a = x` we swap the roles of the two edges.
-/
lemma splitsAt_of_not_reachable {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
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
For the second case of the colouring argument, we show that if `G` splits at no
vertex then all its edges lie in a single block. We first show this for two edges
`x — u` and `x — w` at a common vertex `x`. If some walk from `u` to `w` avoids `x`,
then shortening it to a path and closing it up with the two edges gives a cycle
through both. Otherwise every walk from `u` to `w` passes through `x`, while
`u — x — w` joins them, so `x` is a cut vertex and `G` splits at `x`.
-/
lemma blockEquivalent_of_adj_of_adj (hG : ∀ x, ¬ G.SplitsAt x) {x u w : V}
    (hu : G.Adj x u) (hw : G.Adj x w) : G.BlockEquivalent s(x, u) s(x, w) := by
  classical
  rcases eq_or_ne u w with rfl | huw
  · exact .refl _
  by_cases! h : ∃ p : G.Walk u w, x ∉ p.support
  · obtain ⟨p, hxp⟩ := h
    have hxP : x ∉ p.bypass.support :=
      fun h => hxp (p.support_bypass_subset_support h)
    -- closing up the path `p.bypass` with the edges `w — x — u` gives a cycle
    have hcyc := (cons_isCycle_iff_length_ne_one _ hu).mpr
      ⟨p.bypass_isPath.concat hxP hw.symm,
        by simpa using fun h => huw (eq_of_length_eq_zero h)⟩
    exact CycleEquivalent.blockEquivalent (.inr ⟨x, _, hcyc, by simp, by simp⟩)
  · exact (hG x (IsCutVertex.splitsAt
      ⟨u, w, hu.ne.symm, hw.ne.symm, hu.symm.reachable.trans hw.reachable, h⟩)).elim

/-!
For two arbitrary edges `a — b` and `c — d` we chain the previous result along a
walk from `a` to `c`. Such a walk exists: otherwise the edges `a — b` and `c — d`
lie in different components, so `G` would split at every vertex.
-/
lemma blockEquivalent_of_not_splitsAt (hG : ∀ x, ¬ G.SplitsAt x) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) : G.BlockEquivalent s(a, b) s(c, d) := by
  have key : ∀ {y} (q : G.Walk y c) {z}, G.Adj y z →
      G.BlockEquivalent s(y, z) s(c, d) := by
    intro y q
    induction q with
    | nil => exact fun hz => blockEquivalent_of_adj_of_adj hG hz hcd
    | @cons u v _ h q ih =>
      intro z hz
      refine (blockEquivalent_of_adj_of_adj hG hz h).trans ?_
      rw [Sym2.eq_swap]
      exact ih hcd h.symm
  by_cases hac : G.Reachable a c
  · exact key hac.some hab
  · exact (hG a (splitsAt_of_not_reachable hab hcd hac a)).elim

/-!
For finite graphs we can now argue by well-founded induction on `G`, with respect to
`<`. This is allowed because there are only finitely many graphs on a finite vertex
type (a graph is determined by its adjacency relation, `SimpleGraph.adj_injective`),
and a strict order on a finite type is well-founded. If `G` splits at some vertex,
then both pieces are proper subgraphs, whose blocks map into blocks of `G` along the
inclusion `Copy.ofLE` (`Block.map_toSubgraph_le`), so we can colour them by induction
and glue the colourings together. Otherwise `G` is either edgeless or all its edges
lie in the block of any one of them, and a colouring of that block extends to `G`
(`Subgraph.colorable_of_forall_adj`).
-/
theorem colorable_of_forall_block [Finite V] {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph V) (hcol : ∀ B : G.Block, B.toSubgraph.coe.Colorable n) :
    G.Colorable n := by
  have : Finite (SimpleGraph V) := .of_injective _ SimpleGraph.adj_injective
  induction G using WellFoundedLT.induction with
  | _ G ih =>
    have hlt : ∀ H < G, H.Colorable n := fun H hH => ih H hH fun B =>
      (hcol _).of_hom (Subgraph.homOfMapLE _
        (B.map_toSubgraph_le (Copy.ofLE _ _ hH.le)))
    by_cases! hs : ∃ x, G.SplitsAt x
    · obtain ⟨x, G₁, G₂, h₁, h₂, hG, hmeet⟩ := hs
      rw [← hG]
      exact Colorable.sup_of_subsingleton_inter hmeet (hlt _ h₁) (hlt _ h₂)
    · by_cases! he : ∃ a b, G.Adj a b
      · obtain ⟨a, b, hab⟩ := he
        exact hab.block.toSubgraph.colorable_of_forall_adj hn
          (fun c d hcd => blockMk_toSubgraph_adj.mpr
            ⟨hcd, blockEquivalent_of_not_splitsAt hs hab hcd⟩) (hcol _)
      · exact ⟨Coloring.mk (fun _ => (⟨0, hn⟩)) fun {a b} hab => (he a b hab).elim⟩

/-!
In the exercises we use the *De Bruijn–Erdős theorem*
(`colorable_of_forall_finite_subgraph_colorable`) to remove the finiteness
assumption: for `n ≥ 1`, any graph is `n`-colourable iff each of its blocks is.
-/

end SimpleGraph
