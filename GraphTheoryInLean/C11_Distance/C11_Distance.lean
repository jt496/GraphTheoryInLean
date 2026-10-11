import GraphTheoryInLean.C06_Cliques.Exercises
import GraphTheoryInLean.C07_Colorings.C07_Colorings
import GraphTheoryInLean.C09_Subgraphs.C09_Subgraphs
import GraphTheoryInLean.C10_Connectivity.C10_Connectivity
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Diam
variable {V : Type*} {G : SimpleGraph V}
namespace SimpleGraph

open Walk

/-!
The *distance* between two vertices of a graph measures how far apart they are: it
is the length of a shortest walk between them. In a connected graph it makes the
vertex set into a metric space, and many of the most natural graph parameters are
defined in terms of it: the *eccentricity* of a vertex, the *diameter* and *radius*
of a graph and, closely related, the *girth*, which is the length of a shortest
cycle.

In this chapter we introduce Mathlib's distance `edist` and its basic properties,
and show that the distance in the hypercube `Q[n]` is the Hamming distance. We study
eccentricity, diameter and radius, with vertex-transitive graphs, the hypercube and
the Mycielskian as examples. We then turn to girth, which we compute for cycle
graphs, complete bipartite graphs, hypercubes and Mycielskians.

Counting the vertices in the distance layers around a vertex gives the *Moore bound*
and the *cage bound*, which relate the number of vertices of a graph to its degrees,
its diameter and its girth, and the Petersen graph shows that both bounds can be
attained. Finally we prove *Albertson's theorem*: a precolouring of vertices that are
pairwise far apart extends to a colouring with one extra colour.

# Graph Distance

The *distance* between two vertices `u` and `v` in a graph `G` is the length of a
shortest walk from `u` to `v` (or infinity if no such walk exists). Mathlib provides
two versions: `G.edist u v` takes values in `ℕ∞` (the extended naturals, where
`⊤ = ∞`), and `G.dist u v` takes values in `ℕ`, with the convention that unreachable
pairs are at distance `0`. In this chapter we will work almost entirely with `edist`,
and pass to `dist` only when a natural number is needed; we explain why in
[Junk Values and dist](https://jt496.github.io/GraphTheoryInLean/Distance/#section-junk-values-and-dist).

[Figure: BFS layers from a root vertex partition $V$ by graph distance](https://jt496.github.io/GraphTheoryInLean/figures/distance_bfs.svg)
-/

#source SimpleGraph.edist -- def edist (u v : V) : ℕ∞ := ⨅ w : G.Walk u v, w.length
#source SimpleGraph.dist  -- def dist (u v : V) : ℕ := (G.edist u v).toNat

/-!
The basic properties of `edist` are all in Mathlib. It is the infimum of the lengths
of the walks from `u` to `v`, so any walk gives an upper bound; it is zero iff the
endpoints coincide and one iff they are adjacent; and it is symmetric and satisfies
the triangle inequality. In other words `edist` makes the vertex set into an extended
metric space.
-/
#check SimpleGraph.edist_eq_sInf         -- G.edist u v = sInf {p.length | p}
#check SimpleGraph.edist_le              -- G.edist u v ≤ ↑p.length
#check SimpleGraph.edist_eq_zero_iff     -- G.edist u v = 0 ↔ u = v
#check SimpleGraph.edist_eq_one_iff_adj  -- G.edist u v = 1 ↔ G.Adj u v
#check SimpleGraph.edist_comm            -- G.edist u v = G.edist v u
#check SimpleGraph.edist_triangle        -- G.edist u w ≤ G.edist u v + G.edist v w

/-!
The distance is finite exactly when the two vertices are reachable from each other,
in which case some walk realizes it. Adding edges can only decrease distances.
-/
#check SimpleGraph.edist_ne_top_iff_reachable
#check SimpleGraph.Reachable.exists_walk_length_eq_edist
#check SimpleGraph.edist_anti  -- G ≤ G' → G'.edist u v ≤ G.edist u v

/-!
The `ℕ`-valued `dist` agrees with `edist` on reachable pairs, and in a connected
graph every distance is realized by a walk.
-/
#check SimpleGraph.Reachable.coe_dist_eq_edist
#check SimpleGraph.Connected.exists_walk_length_eq_dist

/-!
## Junk Values and `dist`

Why do we prefer `edist`? The triangle inequality for `edist` holds for all vertices,
with no hypotheses. For `dist` it can fail: if `u — w` is an edge and `v` is an
isolated vertex, then `G.dist u w = 1`, while `G.dist u v + G.dist v w = 0 + 0`,
because `0` is also the value that `dist` takes on unreachable pairs. So Mathlib's
triangle inequalities for `dist` need a connectivity or reachability hypothesis.
-/
#check SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable
#check SimpleGraph.Connected.dist_triangle
#check SimpleGraph.Reachable.dist_triangle_left

/-!
This is the convention for cardinalities from
[Counting in ℕ∞ : ENat.card](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-counting-in-enat-card)
again: `Nat.card α` is `(ENat.card α).toNat`, so an infinite type has `Nat.card`
equal to `0`, just as `G.dist u v` is `(G.edist u v).toNat`, which sends `⊤` to `0`.
Each `ℕ∞`-valued parameter in this chapter is related to its `ℕ`-valued version in
the same way, and we will point out the places where the junk value changes what a
theorem can say.

## Distance under Homomorphisms and Isomorphisms

A graph homomorphism does not increase distances, since it maps a shortest walk to a
walk of the same length, and consequently a graph isomorphism preserves them. Neither
fact is in Mathlib, but both are easy, and we will use them repeatedly: to show that
automorphisms preserve eccentricities, and in
[Algebraic Graph Theory](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#chapter-algebraic-graph-theory)
to transport the distance between two constructions of the hypercube.
-/
lemma Hom.edist_le {W : Type*} {H : SimpleGraph W} (e : G →g H) (u v : V) :
    H.edist (e u) (e v) ≤ G.edist u v :=
  le_iInf fun p => (p.map e).edist_le.trans_eq (by simp)

/-!
A graph isomorphism preserves the graph distance.
-/
lemma Iso.edist_eq {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.edist (e u) (e v) = G.edist u v := by
  refine le_antisymm (e.toHom.edist_le u v) ?_
  simpa using e.symm.toHom.edist_le (e u) (e v)

/-!
## Distance in Box Products

The distance in a box product is the sum of the distances in its two factors: a walk
in `G □ H` moves in one coordinate at a time, so it projects to a walk in each
factor, and conversely walks in the two factors can be run one after the other.
Mathlib records this as `edist_boxProd`. Together with the distance in a complete
graph, `edist_top`, it will let us compute distances in the hypercube, which we
defined as an iterated box product in
[Hypercube](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-hypercube).
-/
#check edist_boxProd  -- (G □ H).edist x y = G.edist x.1 y.1 + H.edist x.2 y.2
#check edist_top      -- (⊤ : SimpleGraph V).edist u v = if u = v then 0 else 1

/-!
## Distance in the Hypercube

As an application we compute the distance in the hypercube `Q[n]`. Since `Q[n + 1]`
is by definition the box product `Q[n] □ ⊤` of `Q[n]` with the complete graph on
`Bool` (`hypercube_succ`), the box product formula `edist_boxProd` splits the
distance in `Q[n + 1]` into the distance in `Q[n]` plus a distance in `⊤`, which is
`0` or `1` according to whether the last coordinates agree (`edist_top`). This is
exactly the recursion defining the Hamming distance `HypercubeVert.hammingDist` of
[Hamming Paths](https://jt496.github.io/GraphTheoryInLean/Walks/#section-hamming-paths),
so by induction the graph distance *is* the Hamming distance.
-/
lemma edist_eq_hammingDist {n : ℕ} {u v : HypercubeVert n} :
    Q[n].edist u v = u.hammingDist v := by
  induction n with
  | zero => simp [HypercubeVert.hammingDist_zero, Subsingleton.elim u v]
  | succ n ih =>
    rw [hypercube_succ, edist_boxProd, ih, edist_top, HypercubeVert.hammingDist_succ]
    split_ifs <;> simp

/-!
In particular the Hamming distance inherits the properties of the graph distance,
such as the triangle inequality. And adjacency in `Q[n]` is exactly "Hamming distance
one", since the adjacent vertices are exactly those at distance one
(`edist_eq_one_iff_adj`).
-/
lemma hypercube_adj_iff_hammingDist_eq_one {n : ℕ} {u v : HypercubeVert n} :
    Q[n].Adj u v ↔ u.hammingDist v = 1 := by
  rw [← edist_eq_one_iff_adj, edist_eq_hammingDist, Nat.cast_eq_one]

/-!
## Distance in Acyclic Graphs

In an acyclic graph there is at most one path between any two vertices
(`IsAcyclic.subsingleton_path`), while a shortest walk is always a path
(`Reachable.exists_path_of_dist`). So in a forest the distance between two vertices
is simply the length of the path joining them.
-/
lemma IsAcyclic.edist_eq_length (hG : G.IsAcyclic) {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) : G.edist u v = p.length := by
  obtain ⟨q, hq, hql⟩ := p.reachable.exists_path_of_dist
  obtain rfl : p = q :=
    congrArg Subtype.val ((hG.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩)
  rw [← p.reachable.coe_dist_eq_edist, hql]

/-!
For example, the infinite path `pathNat₁` is a tree
([The Infinite Path Is a Tree](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-the-infinite-path-is-a-tree)).
In
[Constructing Walks](https://jt496.github.io/GraphTheoryInLean/Walks/#section-constructing-walks)
we built the walk `pathNat₁Walk m k = m — m + 1 — ⋯ — m + k` of length `k`, and in
[Trails and Paths](https://jt496.github.io/GraphTheoryInLean/Walks/#section-trails-and-paths)
we showed that it is a path. Hence the distance from `m` to `m + k` is `k`.
-/
#check Walk.length_pathNat₁Walk -- (pathNat₁Walk i j).length = j
#check Walk.isPath_pathNat₁Walk -- (pathNat₁Walk i j).IsPath

lemma edist_pathNat₁ (m k : ℕ) : pathNat₁.edist m (m + k) = k := by
  rw [pathNat₁_isAcyclic.edist_eq_length (isPath_pathNat₁Walk m k),
    length_pathNat₁Walk]

/-!
# Eccentricity, Diameter and Radius

For a vertex `v`, its *eccentricity* is the maximum distance from `v` to any other
vertex. The *diameter* is the maximum eccentricity, and the *radius* is the minimum.
The vertices whose eccentricity equals the radius form the *centre* of the graph. As
with the distance, Mathlib provides an `ℕ∞`-valued diameter `ediam` and an
`ℕ`-valued `diam`. The eccentricity and the radius come only in `ℕ∞`-valued
versions.

[Figure: A graph of radius 2 and diameter 4 with a diametric path highlighted](https://jt496.github.io/GraphTheoryInLean/figures/eccentricity.svg)
-/

#check SimpleGraph.eccent  -- G.eccent v : ℕ∞  (max distance from v)
#check SimpleGraph.ediam   -- G.ediam : ℕ∞     (max over all v of eccent v)
#check SimpleGraph.diam    -- G.diam : ℕ       (`G.ediam.toNat`)
#check SimpleGraph.radius  -- G.radius : ℕ∞    (min over all v of eccent v)
#check SimpleGraph.center  -- G.center : Set V (vertices of minimum eccentricity)

/-!
The eccentricity and the diameter bound pairwise distances, and conversely a bound on
all distances bounds the eccentricity and the diameter.
-/
#check SimpleGraph.edist_le_eccent  -- G.edist u v ≤ G.eccent u
#check SimpleGraph.edist_le_ediam   -- G.edist u v ≤ G.ediam
#check SimpleGraph.eccent_le_iff    -- G.eccent u ≤ k ↔ ∀ v, G.edist u v ≤ k
#check SimpleGraph.ediam_le_iff     -- G.ediam ≤ k ↔ ∀ u v, G.edist u v ≤ k

/-!
A finite graph on a nonempty vertex type is connected iff its diameter is finite, in
which case the diameter is attained by some pair of vertices.
-/
#check SimpleGraph.connected_iff_ediam_ne_top
#check SimpleGraph.exists_edist_eq_ediam_of_ne_top

/-!
The finiteness hypothesis cannot be dropped. The infinite path `pathNat₁` is
connected (`pathNat₁_connected`), but the distance from `0` to `k` is `k`
(`edist_pathNat₁`), so its diameter is `⊤`. Its `ℕ`-valued diameter is therefore the
junk value `0`.

In the proof, `ediam_eq_top` gives us some `b : ℕ∞` with `b < ⊤`, which we `lift`
to `ℕ`.
-/
lemma ediam_pathNat₁ : pathNat₁.ediam = ⊤ := by
  refine ediam_eq_top.mpr fun b hb => ?_
  lift b to ℕ using hb.ne
  exact ⟨0, b + 1, by rw [← zero_add (b + 1), edist_pathNat₁]; norm_cast; grind⟩

lemma diam_pathNat₁ : pathNat₁.diam = 0 :=
  diam_eq_zero_of_ediam_eq_top ediam_pathNat₁

/-!
The radius is at most the diameter, provided that there is at least one vertex: a
graph with no vertices has radius `⊤`, an infimum over no vertices, but diameter
`0`. And the diameter is at most twice the radius (by the triangle inequality via a
central vertex).
-/
#check SimpleGraph.radius_le_eccent         -- G.radius ≤ G.eccent u
#check SimpleGraph.radius_le_ediam          -- [Nonempty α] : G.radius ≤ G.ediam
#check SimpleGraph.radius_eq_top_of_isEmpty -- [IsEmpty α] : G.radius = ⊤
#check SimpleGraph.ediam_le_two_mul_radius  -- G.ediam ≤ 2 * G.radius

/-!
The complete graph on at least two vertices has diameter and radius `1`, and it is
the only graph with diameter `1`.
-/
#check SimpleGraph.diam_top      -- [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1
#check SimpleGraph.radius_top    -- [Nontrivial α] : (⊤ : SimpleGraph α).radius = 1
#check SimpleGraph.ediam_eq_one  -- [Nontrivial α] : G.ediam = 1 ↔ G = ⊤

/-!
## Distance Invariants under Isomorphism

Since isomorphisms preserve distances they preserve eccentricities, and hence the
diameter and the radius are isomorphism invariants.
-/
lemma Iso.eccent_eq {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u : V) :
    H.eccent (e u) = G.eccent u :=
  (e.toEquiv.iSup_comp (g := H.edist (e u))).symm.trans (iSup_congr (e.edist_eq u))

lemma Iso.ediam_eq {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    G.ediam = H.ediam :=
  (iSup_congr fun u => (e.eccent_eq u).symm).trans
    (e.toEquiv.iSup_comp (g := H.eccent))

lemma Iso.radius_eq {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    G.radius = H.radius :=
  (iInf_congr fun u => (e.eccent_eq u).symm).trans
    (e.toEquiv.iInf_comp (g := H.eccent))

/-!
In a vertex-transitive graph
([Vertex-Transitivity](https://jt496.github.io/GraphTheoryInLean/Maps/#section-vertex-transitivity))
all eccentricities coincide, so the radius equals the diameter and every vertex is
central. We use this below to compute the radius of the hypercube from its diameter.
-/
lemma IsVertexTransitive.eccent_eq (h : G.IsVertexTransitive) (u v : V) :
    G.eccent u = G.eccent v := by
  obtain ⟨f, hf⟩ := h u v
  rw [← hf, f.eccent_eq]

lemma IsVertexTransitive.radius_eq_ediam [Nonempty V] (h : G.IsVertexTransitive) :
    G.radius = G.ediam :=
  radius_eq_ediam_iff.mpr
    ⟨G.eccent (Classical.arbitrary V),
      fun u => h.eccent_eq u _⟩

lemma IsVertexTransitive.center_eq_univ [Nonempty V] (h : G.IsVertexTransitive) :
    G.center = Set.univ :=
  center_eq_univ_iff_radius_eq_ediam.mpr h.radius_eq_ediam

/-!
## Diameter of Box Products

Since distances add in a box product, so do diameters, provided both factors have a
vertex (if one factor is empty then so is the product, and its diameter is `0`). The
upper bound is immediate from `edist_boxProd`. For the lower bound we write each
diameter as a single supremum over pairs of vertices (`ediam_def`) and use
`ENat.iSup_add_iSup_le`, which bounds a sum of two suprema term by term.
-/
lemma ediam_boxProd {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    [Nonempty α] [Nonempty β] : (G □ H).ediam = G.ediam + H.ediam := by
  refine le_antisymm (ediam_le_of_edist_le fun x y => ?_) ?_
  · rw [edist_boxProd]
    exact add_le_add edist_le_ediam edist_le_ediam
  · rw [ediam_def, ediam_def]
    refine ENat.iSup_add_iSup_le fun p q => ?_
    simpa using edist_le_ediam (G := G □ H) (u := (p.1, q.1)) (v := (p.2, q.2))

/-!
## Diameter and Radius of the Hypercube

Diameters add under box products (`ediam_boxProd`) and the complete graph on `Bool`
has diameter `1` (`ediam_top`), so by induction the diameter of `Q[n]` is `n`. The
base case is the one-vertex graph `Q[0]`, whose diameter is `0`
(`ediam_eq_zero_of_subsingleton`); we gave `HypercubeVert 0` a `Subsingleton`
instance back in
[Computations with Hypercubes](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-computations-with-hypercubes).
-/
lemma ediam_hypercube {n : ℕ} : Q[n].ediam = n := by
  induction n with
  | zero => exact ediam_eq_zero_of_subsingleton
  | succ n ih => rw [hypercube_succ, ediam_boxProd, ih, ediam_top, Nat.cast_succ]

lemma diam_hypercube {n : ℕ} : Q[n].diam = n := by
  rw [SimpleGraph.diam, ediam_hypercube, ENat.toNat_natCast]

/-!
Since the hypercube is vertex-transitive (`isVertexTransitive_hypercube`) its radius
equals its diameter, and every vertex is central.
-/
lemma radius_hypercube {n : ℕ} : Q[n].radius = n := by
  rw [(isVertexTransitive_hypercube n).radius_eq_ediam, ediam_hypercube]

/-!
## Distances in the Mycielskian

If `G` is a graph without isolated vertices then, whatever the diameter of `G`, its
Mycielskian has radius at most `2` and diameter at most `4`. The apex `none` is
adjacent to every right copy `v ᵣ`, and each left copy `v ₗ` is at distance at most
`2` from the apex, via the right copy of any neighbour of `v`.
-/
@[simp]
lemma mycielskian_edist_none_right {v : V} : mμ[G].edist none v ᵣ = 1 := by
  simp [edist_eq_one_iff_adj]

lemma mycielskian_edist_none_left_le_two {u v : V} (h : G.Adj u v) :
    mμ[G].edist none v ₗ ≤ 2 := by
  have h1 : mμ[G].Adj none u ᵣ := by simp
  have h2 : mμ[G].Adj u ᵣ v ₗ := by simpa
  exact edist_le (cons h1 <| cons h2 nil)

theorem mycielskian_radius_le_two (h : ∀ v : V, ∃ u : V, G.Adj v u) :
    mμ[G].radius ≤ 2 := by
  refine radius_le_eccent.trans ((eccent_le_iff none _).mpr ?_)
  rintro (_ | ⟨v | v⟩)
  · simp
  · obtain ⟨u, hu⟩ := h v
    exact mycielskian_edist_none_left_le_two hu.symm
  · simp

theorem mycielskian_ediam_le_four (h : ∀ v : V, ∃ u : V, G.Adj v u) :
    mμ[G].ediam ≤ 4 :=
  ediam_le_two_mul_radius.trans <| by grw [mycielskian_radius_le_two h]; rfl

/-!
The `ℕ`-valued version of the bound, on the other hand, needs no hypothesis at all,
since the diameter of a disconnected graph is the junk value `0`. Here the junk value
removes a hypothesis, but only because the `ℕ`-valued statement says nothing about
the disconnected case.
-/
theorem mycielskian_diam_le_four : mμ[G].diam ≤ 4 := by
  by_cases h : ∀ v : V, ∃ u : V, G.Adj v u
  · exact ENat.toNat_le_of_le_natCast (mycielskian_ediam_le_four h)
  · -- an isolated vertex `v` of `G` makes `v ₗ` isolated in `mμ[G]`
    obtain ⟨v, hv⟩ := not_forall.mp h
    refine (diam_eq_zero_of_not_connected fun hc => ?_).trans_le (by norm_num)
    obtain ⟨p⟩ := hc.preconnected (v ₗ) none
    cases p with
    | cons ha _ =>
      rename_i x _
      rcases x with _ | x | x <;> simp_all

/-!
# Girth

The *girth* of a graph is the length of its shortest cycle. Mathlib again provides
two versions: `G.egirth : ℕ∞`, which is `⊤` for an acyclic graph, and `G.girth : ℕ`,
which is `0` for an acyclic graph. Girth is the natural companion of the diameter: if
the maximum degree is bounded, small diameter forces *few* vertices, while if the
minimum degree is bounded below, large girth forces *many*. These are the Moore and
cage bounds of
[Moore and Cage Bounds](https://jt496.github.io/GraphTheoryInLean/Distance/#section-moore-and-cage-bounds).
Girth also enters the Mycielski construction: `mμ[G]` raises the chromatic number
([Colouring Mycielskians](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-colouring-mycielskians))
while staying triangle-free
([Triangle-Free Mycielskians](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-triangle-free-mycielskians)),
and below we compute its girth exactly.

[Figure: A graph with its shortest cycle highlighted](https://jt496.github.io/GraphTheoryInLean/figures/girth.svg)
-/

#check egirth  -- G.egirth : ℕ∞
#check girth   -- G.girth : ℕ

/-!
The girth is infinite (respectively zero) iff the graph is acyclic, and any cycle
bounds it above. Every cycle has length at least `3`, so `egirth` is always at least
`3`, but `girth` is at least `3` only for a graph with a cycle, because of the junk
value `0`.
-/
#check egirth_eq_top                  -- G.egirth = ⊤ ↔ G.IsAcyclic
#check girth_eq_zero                  -- G.girth = 0 ↔ G.IsAcyclic
#check Walk.IsCycle.egirth_le_length  -- p.IsCycle → G.egirth ≤ p.length
#check three_le_egirth                -- 3 ≤ G.egirth
#check three_le_girth                 -- ¬G.IsAcyclic → 3 ≤ G.girth

/-!
Girth and diameter are related: a shortest cycle has length at most `2 * diam + 1`,
since otherwise two antipodal vertices of the cycle would be joined by a shorter
path, producing a shorter cycle. Mathlib states this in three ways, and their
hypotheses show the junk values at work.

* For `egirth` we must exclude acyclic graphs, whose `egirth` is `⊤`.
* For `girth` no hypothesis is needed: the junk value `0` of an acyclic graph
  satisfies the bound anyway.
* To use `diam` instead of `ediam` we must assume that the diameter is finite, since
  otherwise `diam` is `0` and the right-hand side is just `1`.

So a junk value sometimes removes a hypothesis and sometimes adds one. The same
happens for containment: a graph containing a copy of `H` has girth at most that of
`H`, and the `girth` version needs `H` to have a cycle. Finally, isomorphisms
preserve the girth.
-/
#check egirth_le_two_mul_ediam_add_one -- ¬G.IsAcyclic → G.egirth ≤ 2 * G.ediam + 1
#check girth_le_two_mul_ediam_add_one  -- G.girth ≤ 2 * G.ediam + 1
#check girth_le_two_mul_diam_add_one   -- G.ediam ≠ ⊤ → G.girth ≤ 2 * G.diam + 1
#check IsContained.egirth_le           -- H ⊑ G → G.egirth ≤ H.egirth
#check IsContained.girth_le            -- H ⊑ G → ¬H.IsAcyclic → G.girth ≤ H.girth
#check Iso.egirth_eq

/-!
A graph has no cycle of length at most `k` exactly when it contains no copy of `C[n]`
for `3 ≤ n ≤ k`, i.e. when it is `C[n]`-free in the language of
[Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies): Mathlib's
`cycleGraph_isContained_iff` says that `G` contains a copy of `C[n]` (for `n ≥ 3`)
iff it has a cycle of length `n`. (Every cycle has length at least `3`, so only
`n ≥ 3` matters; `C[2]` is a single edge.) Excluding these copies therefore bounds
the girth from below.
-/
lemma le_egirth_of_free {k : ℕ} (h : ∀ n, 3 ≤ n → n ≤ k → C[n].Free G) :
    k + 1 ≤ G.egirth := by
  rw [le_egirth]
  intro a w hw
  by_contra! hlt
  have hk : w.length ≤ k := by exact_mod_cast Order.le_of_lt_add_one hlt
  have h3 := hw.three_le_length
  exact h _ h3 hk ((cycleGraph_isContained_iff (by grind)).mpr ⟨_, _, hw, rfl⟩)

/-!
Being triangle-free is the case `n = 3`: `C[3]` is the complete graph on three
vertices (`cycleGraph_three_eq_top`), and Mathlib's `cliqueFree_iff_free_top_fin`
identifies `G.CliqueFree n` with being `K[n]`-free.
-/
lemma cliqueFree_three_iff_free_cycleGraph : G.CliqueFree 3 ↔ C[3].Free G := by
  rw [cycleGraph_three_eq_top, cliqueFree_iff_free_top_fin]

/-!
So a triangle-free graph has girth at least `4`, and if it also contains no copy of
`C[4]` then its girth is at least `5`.
-/
lemma four_le_egirth_of_cliqueFree_three (h : G.CliqueFree 3) : 4 ≤ G.egirth :=
  le_egirth_of_free fun n h3 hn => by
    obtain rfl : n = 3 := by grind
    exact cliqueFree_three_iff_free_cycleGraph.mp h

lemma five_le_egirth (h3 : G.CliqueFree 3) (h4 : C[4].Free G) : 5 ≤ G.egirth :=
  le_egirth_of_free fun n h3n hn => by
    obtain rfl | rfl : n = 3 ∨ n = 4 := by grind
    exacts [cliqueFree_three_iff_free_cycleGraph.mp h3, h4]

/-!
## Girth and Diameter of Cycle Graphs

The cycle graph `C[n + 3]` contains the cycle `cycleGraph.cycle n` of length `n + 3`,
so its girth is at most `n + 3`. For the reverse inequality we use a fact from
[Odd Cycles and Bipartite Graphs](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-odd-cycles-and-bipartite-graphs):
in a connected graph in which every vertex has degree at most `2`, every cycle is a
Hamiltonian cycle (`Walk.IsCycle.isHamiltonianCycle_of_degree_le_two`). The cycle
graph is connected (`cycleGraph_connected`), and each vertex `v` has degree at most
`2`, since Mathlib's `cycleGraph_degree_two_le` says that its neighbours are `v - 1`
and `v + 1`. A Hamiltonian cycle has length equal to the number of vertices
(`Walk.IsHamiltonianCycle.length_eq`), so every cycle in `C[n + 3]` has length
exactly `n + 3`.
-/
lemma egirth_cycleGraph (n : ℕ) : (cycleGraph (n + 3)).egirth = n + 3 := by
  refine le_antisymm ?_ ?_
  · simpa using cycleGraph.isCycle_cycle.egirth_le_length
  · rw [le_egirth]
    intro a w hw
    rw [(hw.isHamiltonianCycle_of_degree_le_two cycleGraph_connected fun v => by
      rw [cycleGraph_degree_two_le]
      exact (Finset.card_insert_le _ _).trans (by simp)).length_eq]
    simp [add_assoc]

/-!
The girth also determines the diameter of `C[n + 3]`. In any graph with a cycle the
girth is at most `2 * ediam + 1` (`egirth_le_two_mul_ediam_add_one`), which here
gives the lower bound `(n + 3) / 2 ≤ ediam`. For the upper bound we use the
vertex-transitivity of cycle graphs
([Vertex-Transitivity](https://jt496.github.io/GraphTheoryInLean/Maps/#section-vertex-transitivity)):
the diameter is the radius, so it is at most the eccentricity of the vertex `0`, and
going one way or the other around `cycleGraph.cycle n` reaches any vertex `a` from
`0` in `a` or `n + 3 - a` steps.
-/
lemma ediam_cycleGraph (n : ℕ) : (cycleGraph (n + 3)).ediam = ((n + 3) / 2 : ℕ) := by
  refine le_antisymm ?_ ?_
  · rw [← (isVertexTransitive_cycleGraph _).radius_eq_ediam]
    refine (radius_le_eccent (u := 0)).trans ((eccent_le_iff _ _).mpr fun v => ?_)
    obtain ⟨a, ha⟩ := v
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    -- `cycleGraph.cycle n` runs backwards: it reaches `a` after `n + 3 - a` steps
    have hv : (cycleGraph.cycle n).getVert (n + 3 - a) = ⟨a, ha⟩ := by
      simp [cycleGraph.getVert_cycle (by grind : n + 3 - a ≤ n + 3),
        Nat.mod_eq_of_lt ha, Nat.sub_sub_self ha.le]
    have h₁ := edist_le (((cycleGraph.cycle n).take (n + 3 - a)).copy rfl hv)
    have h₂ := edist_le (((cycleGraph.cycle n).drop (n + 3 - a)).copy hv rfl).reverse
    simp only [length_copy, length_reverse, take_length, drop_length,
      cycleGraph.length_cycle] at h₁ h₂
    rcases le_total a (n + 3 - a) with h | h
    · exact h₂.trans (Nat.cast_le.mpr (by grind))
    · exact h₁.trans (Nat.cast_le.mpr (by grind))
  · have h := egirth_le_two_mul_ediam_add_one (G := cycleGraph (n + 3))
      fun hG => hG _ cycleGraph.isCycle_cycle
    rw [egirth_cycleGraph] at h
    lift (cycleGraph (n + 3)).ediam to ℕ
      using connected_iff_ediam_ne_top.mp cycleGraph_connected with m
    norm_cast at h ⊢
    grind

/-!
## The Girth of Complete Bipartite Graphs

A bipartite graph is triangle-free, since a `2`-colourable graph contains no
`3`-clique (`Colorable.cliqueFree`), so its girth is at least `4`. When both sides
have at least two vertices the complete bipartite graph contains a `4`-cycle, so its
girth is exactly `4`.
-/
lemma egirth_completeBipartiteGraph (s t : ℕ) : K[s + 2, t + 2].egirth = 4 := by
  refine le_antisymm ?_ (four_le_egirth_of_cliqueFree_three (Colorable.cliqueFree
    ((completeBipartiteGraph.bicoloring _ _).colorable : K[s + 2, t + 2].Colorable 2)
    (by norm_num)))
  let c : K[s + 2, t + 2].Walk (.inl 0) (.inl 0) :=
    cons (by simp : K[s + 2, t + 2].Adj (.inl 0) (.inr 0)) <|
    cons (by simp : K[s + 2, t + 2].Adj (.inr 0) (.inl 1)) <|
    cons (by simp : K[s + 2, t + 2].Adj (.inl 1) (.inr 1)) <|
    cons (by simp : K[s + 2, t + 2].Adj (.inr 1) (.inl 0)) nil
  have hc : c.IsCycle := by simp [c, cons_isCycle_iff]
  simpa [c] using hc.egirth_le_length

/-!
## The Girth of the Hypercube

The hypercube is triangle-free (`hypercube_cliqueFree_three`), so its girth is at
least `4`, and for `n ≥ 2` it contains a `4`-cycle: in `Q[2]` the Gray-code
Hamiltonian cycle `grayCycle 0` of
[Exercises](https://jt496.github.io/GraphTheoryInLean/Walks/#section-exercises-walks)
is one. Each larger cube contains a copy of the previous one, via the embedding
`hypercube.embedFalse`, and a graph containing a copy of `H` has girth at most that
of `H` (Mathlib's `IsContained.egirth_le`).
-/
lemma egirth_hypercube {n : ℕ} : egirth Q[n + 2] = 4 := by
  refine le_antisymm ?_
    (four_le_egirth_of_cliqueFree_three (hypercube_cliqueFree_three _))
  induction n with
  | zero => exact (grayCycle_isHamiltonianCycle 0).isCycle.egirth_le_length
  | succ n ih =>
    exact (IsContained.egirth_le ⟨(hypercube.embedFalse _).toCopy⟩).trans ih

/-!
## The Girth of the Mycielskian

The Mycielskian of a triangle-free graph is triangle-free, so its girth is at least
`4`. Whether it is exactly `4` depends on whether `G` has two edges sharing an
endpoint: if it does, the two edges give a `4`-cycle through the apex; if not, `G` is
a matching plus isolated vertices, and then the girth of `mμ[G]` is `5` provided `G`
has an edge. (If `G` has no edges then `mμ[G]` is a star centred at the apex plus
isolated vertices, so it is acyclic.)
-/
/-- If no two edges share a common endpoint, that is, every vertex has at most one
neighbour, then `G` is a matching plus isolated vertices. -/
abbrev IsMatchingAndIsolated (G : SimpleGraph V) : Prop :=
  ∀ x y z : V, G.Adj x y → G.Adj x z → y = z

/-!
Any pair of edges with a common endpoint, `u — v` and `u — w`, gives rise to a
`4`-cycle in the Mycielskian, `none — v ᵣ — u ₗ — w ᵣ — none`.
-/
def mycielskianFourCycle {u v w : V} (h1 : G.Adj u v) (h2 : G.Adj u w) :
    mμ[G].Walk none none :=
  cons (by simp : mμ[G].Adj none v ᵣ) <| cons (by simp [h1.symm])
    <| cons (by simpa : mμ[G].Adj u ₗ w ᵣ) <| cons (by simp) nil

lemma mycielskianFourCycle_isCycle {u v w : V} (h1 : G.Adj u v) (h2 : G.Adj u w)
    (h : v ≠ w) : (mycielskianFourCycle h1 h2).IsCycle := by
  simp [mycielskianFourCycle, cons_isCycle_iff, h]

lemma length_mycielskianFourCycle {u v w : V} (h1 : G.Adj u v) (h2 : G.Adj u w) :
    (mycielskianFourCycle h1 h2).length = 4 := rfl

/-!
If `G` is triangle-free and is not a matching plus isolated vertices, then `mμ[G]`
has girth `4`.
-/
lemma egirth_mycielskian_eq_four (h3 : G.CliqueFree 3)
    (hnm : ¬G.IsMatchingAndIsolated) : egirth mμ[G] = 4 := by
  obtain ⟨x, y, z, h1, h2, hvw⟩ : ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ y ≠ z := by grind
  refine le_antisymm ?_ (four_le_egirth_of_cliqueFree_three h3.mycielskian)
  simpa [length_mycielskianFourCycle] using
    (mycielskianFourCycle_isCycle h1 h2 hvw).egirth_le_length

/-!
If `G` is a matching then `mμ[G]` contains no copy of `C[4]`. Informally: if a
`4`-cycle passes through the apex, then the vertex opposite the apex is a left copy
`w ₗ` adjacent to the right copies of two different neighbours of `w`. Otherwise the
two neighbours on the cycle of any vertex `y ₗ` or `y ᵣ` are copies of neighbours of
`y`, so (as `G` is a matching) they are the two copies of a single vertex. This
forces two right copies to be adjacent, which is impossible.

In Lean, given a copy `f`, we split into cases according to whether each of
`f 0, …, f 3` is the apex, a left copy or a right copy. The adjacency rules of the
Mycielskian dispose of most of the `81` cases, and the rest contradict `hmatch`.
-/
lemma cycleGraph_four_free_mycielskian (hmatch : G.IsMatchingAndIsolated) :
    C[4].Free mμ[G] := fun ⟨f⟩ => by
  have hadj {i j : Fin 4} (h : C[4].Adj i j) : mμ[G].Adj (f i) (f j) :=
    f.toHom.map_adj h
  have h01 := hadj (i := 0) (j := 1) (by decide)
  have h12 := hadj (i := 1) (j := 2) (by decide)
  have h23 := hadj (i := 2) (j := 3) (by decide)
  have h30 := hadj (i := 3) (j := 0) (by decide)
  have hne02 : f 0 ≠ f 2 := fun h => absurd (f.injective h) (by decide)
  have hne13 : f 1 ≠ f 3 := fun h => absurd (f.injective h) (by decide)
  clear hadj
  generalize f 0 = p0, f 1 = p1, f 2 = p2, f 3 = p3 at *
  rcases p0 with _ | (u | u) <;> rcases p1 with _ | (v1 | v1) <;>
  rcases p2 with _ | (v2 | v2) <;> rcases p3 with _ | (v3 | v3) <;>
  -- 81 goals..
  simp_all only [mycielskian_adj] <;>
  -- 13 goals remain
  first
    | grind
    | have heq := hmatch _ _ _ h12.symm h23 ; grind
    | have heq := hmatch _ _ _ h01 h30.symm ; grind
    | have heq := hmatch _ _ _ h01.symm h12 ; grind
    | have heq := hmatch _ _ _ h23.symm h30 ; grind

/-!
A graph in which no two edges share a common endpoint is triangle-free.
-/
lemma IsMatchingAndIsolated.cliqueFree_three (hmatch : G.IsMatchingAndIsolated) :
    G.CliqueFree 3 := fun t ht => by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
  exact hbc.ne (hmatch a b c hab hac)

/-!
If `G` has an edge and is a matching plus isolated vertices, then `mμ[G]` has girth
`5`.
-/
lemma egirth_mycielskian_eq_five {u v : V} (hedge : G.Adj u v)
    (hmatch : G.IsMatchingAndIsolated) : egirth mμ[G] = 5 := by
  refine le_antisymm ?_ (five_le_egirth hmatch.cliqueFree_three.mycielskian
    (cycleGraph_four_free_mycielskian hmatch))
  simpa [mycielskianClosed] using
    (isCycle_mycielskianClosed_of_adj hedge).egirth_le_length

/-!
The `5`-cycle `isCycle_mycielskianClosed_of_adj` exists for every edge of `G`, so the
Mycielskian of any graph with an edge has girth at most `5`, however large the girth
of `G`. So Mycielski's construction gives triangle-free graphs of large chromatic
number, but not graphs of large girth and large chromatic number. That such graphs
exist is a famous theorem of Erdős (1959), proved by the probabilistic method.
-/

/-!
# Moore and Cage Bounds

Fix a vertex `r` (for *root*). The *distance layers* around `r` are the sets of
vertices at distance exactly `0, 1, 2, …` from `r`: they are the levels of a
breadth-first search tree rooted at `r`, as in the figure at the start of the
chapter. Comparing the sizes of consecutive layers gives two classical bounds
relating the number of vertices of a graph to its degrees, its diameter and its
girth.

* The *Moore bound*: a graph with maximum degree at most `d + 1` and diameter at most
  `k` has at most `1 + (d + 1) * (1 + d + ⋯ + d ^ (k - 1))` vertices.
* The *cage bound*: a graph with minimum degree at least `δ + 1` and girth at least
  `2 * k + 1` has at least `1 + (δ + 1) * (1 + δ + ⋯ + δ ^ (k - 1))` vertices.

(We write the degrees as `d + 1` and `δ + 1` so that the formulas involve no
truncated subtraction in `ℕ`.)

*Sketch proof*: write `Lᵢ` for the `i`-th layer around `r`, so `L₀ = {r}` and `L₁` is
the neighbourhood of `r`.

* Moore: each `u ∈ Lᵢ` with `i ≥ 1` has a neighbour in `Lᵢ₋₁`, so it has at most `d`
  neighbours in `Lᵢ₊₁`. Hence `#Lᵢ₊₁ ≤ d * #Lᵢ`, and if the diameter is at most `k`
  then the layers `L₀, …, Lₖ` cover `V`.
* Cage: if the girth is at least `2 * k + 1` then the graph looks like a tree near
  `r`. For `1 ≤ i < k`, all the neighbours of `u ∈ Lᵢ` but one lie in `Lᵢ₊₁`, and
  two vertices of `Lᵢ` have no common neighbour there, since otherwise there would
  be a cycle of length at most `2 * i + 2 ≤ 2 * k`. Hence `#Lᵢ₊₁ ≥ δ * #Lᵢ`, and the
  disjoint layers `L₀, …, Lₖ` contain the claimed number of vertices.
-/
/-!
## Distance Layers

We need two simple facts about distances from a fixed vertex `r`. Adjacent vertices
have distances from `r` that differ by at most one, and a vertex at distance `i + 1`
from `r` has a neighbour at distance `i`, namely the second-to-last vertex of a
shortest walk from `r`.
-/
lemma Adj.edist_le_add_one {u v : V} (r : V) (h : G.Adj u v) :
    G.edist r v ≤ G.edist r u + 1 := by
  simpa [edist_eq_one_iff_adj.mpr h] using
    G.edist_triangle (u := r) (v := u) (w := v)

lemma exists_adj_edist_eq {r v : V} (i : ℕ) (h : G.edist r v = i + 1) :
    ∃ u, G.Adj u v ∧ G.edist r u = i := by
  -- a shortest walk from `v` back to `r` starts with an edge `v — u`
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe (k := i + 1)
    (by rw [edist_comm]; exact_mod_cast h)
  cases p with
  | nil => simp at hp
  | @cons _ u _ hadj q =>
    refine ⟨u, hadj.symm, le_antisymm ?_ ?_⟩
    · rw [edist_comm]
      exact (edist_le q).trans_eq (by simpa using hp)
    · have := hadj.symm.edist_le_add_one r
      rwa [h, ENat.add_le_add_iff_right ENat.one_ne_top] at this

/-!
To count vertices in each layer we package them as `Finset`s, so from now on we
assume that the vertex type is finite; we return to this assumption in
[Finite Eccentricity](https://jt496.github.io/GraphTheoryInLean/Distance/#section-finite-eccentricity).
The predicate `G.edist r v = i` is decidable, since `ℕ∞` has decidable equality, so
the set-builder notation produces a `Finset`. But `edist` itself is noncomputable (it
is an infimum over all walks), so the definition must be marked `noncomputable`. For
the same reason `decide` cannot evaluate distances: even
`(⊤ : SimpleGraph (Fin 2)).edist 0 1 = 1` cannot be proved by `decide`.

Since `layer` is noncomputable anyway, a `Fintype V` argument would be pointless, so
we assume only `[Finite V]` and pick a `Fintype` instance inside the definition with
`Fintype.ofFinite`. As a bonus, no lemma about layers depends on a choice of
`Fintype` instance (see
[Stating Results Across a Diamond*](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-stating-results-across-a-diamond)).
-/
/-- The `i`-th *distance layer* around `r`: the vertices at distance exactly `i`
from `r`. -/
noncomputable def layer [Finite V] (G : SimpleGraph V) (r : V) (i : ℕ) :
    Finset V :=
  haveI := Fintype.ofFinite V
  {v | G.edist r v = i}

/-!
We first prove some very basic but useful facts about layers.
-/
@[simp]
lemma mem_layer [Finite V] {r v : V} {i : ℕ} :
    v ∈ G.layer r i ↔ G.edist r v = i := by
  simp [layer]

lemma layer_zero [Finite V] (r : V) : G.layer r 0 = {r} := by
  ext v
  simp only [mem_layer, Nat.cast_zero, edist_eq_zero_iff, Finset.mem_singleton]
  exact eq_comm

lemma layer_one [Finite V] [G.LocallyFinite] (r : V) :
    G.layer r 1 = G.neighborFinset r := by
  ext v
  simp [edist_eq_one_iff_adj]

lemma disjoint_layer [Finite V] {r : V} {i j : ℕ} (h : i ≠ j) :
    Disjoint (G.layer r i) (G.layer r j) :=
  Finset.disjoint_left.2 fun v hi hj => h (by simp_all)

/-!
## Counting Between Layers

Both bounds compare consecutive layers by counting the edges between them, using two
double-counting lemmas about finsets `A` and `B` of vertices. Here
`G.degIn B u = #{v ∈ B | G.Adj u v}` is the number of neighbours of `u` in `B`, as in
[Neighbours in a Set](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-neighbours-in-a-set).

We count the adjacent pairs `(u, v)` with `u ∈ A` and `v ∈ B`.

* If every vertex of `B` has a neighbour in `A`, and every vertex of `A` has at most
  `d` neighbours in `B`, then `#B ≤ d * #A`, since each `v ∈ B` lies in at least one
  such pair and each `u ∈ A` in at most `d`.
* If every vertex of `A` has at least `δ` neighbours in `B`, and no two distinct
  vertices of `A` have a common neighbour in `B`, then `δ * #A ≤ #B`, since now each
  `u ∈ A` lies in at least `δ` pairs and each `v ∈ B` in at most one.

Both are instances of Mathlib's double-counting lemmas
`Finset.card_mul_le_card_mul'` and `Finset.card_mul_le_card_mul`. In their language
the neighbours of `u` in `B` form `B.bipartiteAbove G.Adj u`, whose size is
`G.degIn B u` by definition, and the neighbours of `v` in `A` form
`A.bipartiteBelow G.Adj v`.
-/
open Finset
lemma card_le_mul_card_of_adj [DecidableRel G.Adj] {A B : Finset V} {d : ℕ}
    (hB : ∀ v ∈ B, ∃ u ∈ A, G.Adj u v) (hA : ∀ u ∈ A, G.degIn B u ≤ d) :
    #B ≤ d * #A := by
  have := card_mul_le_card_mul' G.Adj (n := 1) (fun v hv => by
    obtain ⟨u, hu, huv⟩ := hB v hv
    exact card_pos.2 ⟨u, (mem_bipartiteBelow _).2 ⟨hu, huv⟩⟩) hA
  grind

lemma mul_card_le_card_of_adj [DecidableRel G.Adj] {A B : Finset V} {δ : ℕ}
    (hA : ∀ u ∈ A, δ ≤ G.degIn B u)
    (hAB : ∀ u ∈ A, ∀ x ∈ A, ∀ v ∈ B, G.Adj u v → G.Adj x v → u = x) :
    δ * #A ≤ #B := by
  have := card_mul_le_card_mul G.Adj hA fun v hv =>
    card_le_one.2 fun u hu x hx => by
      rw [mem_bipartiteBelow] at hu hx
      exact hAB u hu.1 x hx.1 v hv hu.2 hx.2
  grind

/-!
To bound `G.degIn B u` in terms of the degree of `u`, we use two lemmas from
[Neighbours in a Set](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-neighbours-in-a-set).
The Moore bound uses `degIn_lt_degree_of_adj_notMem`: if some neighbour of `u` lies
outside `B` then `G.degIn B u < G.degree u`. The cage bounds need
`degree_le_degIn_add_one`, a bound in the other direction: if every neighbour of `u`,
except possibly `w`, lies in `B`, then `G.degree u ≤ G.degIn B u + 1`.
-/
#check degIn_lt_degree_of_adj_notMem
#check degree_le_degIn_add_one

/-!
## The Moore Bound

In a graph of maximum degree at most `d + 1`, a vertex `u` in the layer `Lᵢ₊₁` has a
neighbour `w ∈ Lᵢ`, which is not in `Lᵢ₊₂`, so `u` has at most `d` neighbours in
`Lᵢ₊₂`. By the first counting lemma, `#Lᵢ₊₂ ≤ d * #Lᵢ₊₁`.
-/
lemma card_layer_add_two_le [Finite V] [G.LocallyFinite] {d : ℕ}
    (h_deg : ∀ v, G.degree v ≤ d + 1) (r : V) (i : ℕ) :
    #(G.layer r (i + 2)) ≤ d * #(G.layer r (i + 1)) := by
  classical
  refine card_le_mul_card_of_adj (G := G) (fun v hv => ?_) (fun u hu => ?_)
  · rw [mem_layer] at hv
    obtain ⟨u, huv, hu⟩ :=
      exists_adj_edist_eq (i + 1) (by rw [hv]; push_cast; ring)
    exact ⟨u, mem_layer.mpr hu, huv⟩
  · -- `u` has a neighbour `w ∈ Lᵢ`, which is not in `Lᵢ₊₂`
    obtain ⟨w, hwu, hw⟩ := exists_adj_edist_eq i (by simpa using hu)
    have := degIn_lt_degree_of_adj_notMem (G.layer r (i + 2)) hwu.symm
      (by simp [hw]; norm_cast; grind)
    grind

/-!
Since `L₁` is the neighbourhood of `r`, induction gives `#Lᵢ₊₁ ≤ (d + 1) * d ^ i`.
-/
lemma card_layer_le [Finite V] [G.LocallyFinite] {d : ℕ}
    (h_deg : ∀ v, G.degree v ≤ d + 1) (r : V) (i : ℕ) :
    #(G.layer r (i + 1)) ≤ (d + 1) * d ^ i := by
  induction i with
  | zero => simpa [layer_one] using h_deg r
  | succ i ih =>
    calc #(G.layer r (i + 2)) ≤ d * #(G.layer r (i + 1)) :=
          card_layer_add_two_le h_deg r i
      _ ≤ d * ((d + 1) * d ^ i) := by gcongr
      _ = (d + 1) * d ^ (i + 1) := by ring

/-!
If every vertex is within distance `k` of `r`, i.e. `G.eccent r ≤ k`, then the layers
`L₀, …, Lₖ` cover `V`, and we can sum these bounds.
-/
theorem card_le_of_eccent_le [Finite V] [G.LocallyFinite] {d k : ℕ}
    (h_deg : ∀ v, G.degree v ≤ d + 1) {r : V} (h : G.eccent r ≤ k) :
    Nat.card V ≤ 1 + (d + 1) * ∑ i ∈ range k, d ^ i := by
  classical
  have := Fintype.ofFinite V
  have hcover : (univ : Finset V) ⊆ (range (k + 1)).biUnion (G.layer r) := by
    intro v _
    have hv : G.edist r v ≤ k := edist_le_eccent.trans h
    lift G.edist r v to ℕ using ne_top_of_le_ne_top (by simp) hv with i hi
    simpa [mem_range] using ⟨i, by exact_mod_cast hv, hi.symm⟩
  calc Nat.card V = #(univ : Finset V) := Nat.card_eq_fintype_card
    _ ≤ #((range (k + 1)).biUnion (G.layer r)) := card_le_card hcover
    _ ≤ ∑ i ∈ range (k + 1), #(G.layer r i) := card_biUnion_le
    _ = ∑ i ∈ range k, #(G.layer r (i + 1)) + 1 := by
        rw [sum_range_succ', layer_zero, card_singleton]
    _ ≤ ∑ i ∈ range k, (d + 1) * d ^ i + 1 := by
        gcongr with i
        exact card_layer_le h_deg r i
    _ = 1 + (d + 1) * ∑ i ∈ range k, d ^ i := by rw [mul_sum, add_comm]

/-!
The Moore bound is usually stated in terms of the diameter, but the proof only uses
a single vertex `r` of eccentricity at most `k`, so a bound on the radius suffices
(the minimum eccentricity is attained, by `exists_eccent_eq_radius`). Since the
radius is at most the diameter this gives the usual form. Note that no connectivity
hypothesis is needed: a finite radius already forces the graph to be connected.
-/
theorem moore_bound_of_radius_le [Finite V] (G : SimpleGraph V) [G.LocallyFinite]
    (d k : ℕ) (h_deg : ∀ v, G.degree v ≤ d + 1) (h : G.radius ≤ k) :
    Nat.card V ≤ 1 + (d + 1) * ∑ i ∈ Finset.range k, d ^ i := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  obtain ⟨r, hr⟩ := exists_eccent_eq_radius (G := G)
  exact card_le_of_eccent_le h_deg (hr ▸ h)

/-!
This gives the Moore bound in its usual form. Here it matters that the hypothesis is
stated with `ediam` rather than `diam`. The empty graph `⊥` on `Fin 2` has maximum
degree `0`, and its `diam` is the junk value `0`, since it is disconnected; but it
has `2` vertices, while the bound with `d = k = 0` is `1`.
-/
theorem moore_bound [Finite V] (G : SimpleGraph V) [G.LocallyFinite] (d k : ℕ)
    (h_deg : ∀ v, G.degree v ≤ d + 1) (h : G.ediam ≤ k) :
    Nat.card V ≤ 1 + (d + 1) * ∑ i ∈ Finset.range k, d ^ i := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  exact moore_bound_of_radius_le G d k h_deg (radius_le_ediam.trans h)

/-!
## Finite Eccentricity

We proved the Moore bound for finite graphs, but what finiteness assumptions are
really needed? The degree hypothesis only makes sense when every vertex has finitely
many neighbours, that is, when `G` is *locally finite*, and this is enough: the
hypotheses of the Moore bound then force `V` to be finite. Indeed, every vertex at
distance at most `i + 1` from `r` is either at distance at most `i` or adjacent to
such a vertex, so by induction each ball around `r` in a locally finite graph is
finite. If `r` has eccentricity at most `k` then `V` is the ball of radius `k` around
`r`.

Mathlib's balls are open: `G.ball r i` is the set of vertices at distance *less*
than `i` from `r`. So the set in the next lemma is `G.ball r (i + 1)`, with the
arguments of `edist` swapped.
-/
#check SimpleGraph.mem_ball  -- v ∈ G.ball c r ↔ G.edist v c < r

lemma finite_setOf_edist_le [G.LocallyFinite] (r : V) (i : ℕ) :
    {v | G.edist r v ≤ i}.Finite := by
  induction i with
  | zero => simp
  | succ i ih =>
    refine (ih.union (ih.biUnion fun u _ => (G.neighborSet u).toFinite)).subset ?_
    intro v (hv : G.edist r v ≤ ↑(i + 1))
    rcases hv.lt_or_eq with hlt | heq
    · push_cast at hlt
      exact Or.inl (Order.le_of_lt_add_one hlt)
    · obtain ⟨u, huv, hu⟩ := exists_adj_edist_eq i (by exact_mod_cast heq)
      exact Or.inr (Set.mem_biUnion (x := u) (by simp [hu]) huv)

/-!
A locally finite graph with a vertex of finite eccentricity is finite.
-/
theorem finite_of_eccent_le [G.LocallyFinite] {r : V} {k : ℕ} (h : G.eccent r ≤ k) :
    Finite V :=
  Set.finite_univ_iff.mp
    ((finite_setOf_edist_le r k).subset fun _ _ => edist_le_eccent.trans h)

/-!
## Short Cycles Between Layers

For the cage bound we need to know that a graph of large girth looks like a tree
near `r`. The key lemma says that if a vertex `v` has two distinct neighbours `a` and
`b`, neither further from `r` than `v`, then `G` has a cycle of length at most
`G.edist r a + G.edist r b + 2`.

To see this, extend shortest walks from `r` to `a` and to `b` by the edges to `v`.
Both resulting walks are *paths*. A shortest walk is a path, and it cannot pass
through `v`, since every vertex on a shortest walk to `a` other than `a` itself is
strictly closer to `r` than `a` is, while `v` is not. The two paths to `v` are
different, since their second-to-last vertices `a ≠ b` differ; so we can apply
`IsPath.exists_isCycle_length_le_add_of_ne` to obtain the desired short cycle.
-/
#check IsPath.exists_isCycle_length_le_add_of_ne

lemma notMem_support_of_length_eq_edist {r a v : V} {p : G.Walk r a}
    (hp : p.length = G.edist r a) (hav : G.edist r a ≤ G.edist r v) (hva : v ≠ a) :
    v ∉ p.support := by
  classical
  intro hv
  have h1 : ((p.takeUntil v hv).length : ℕ∞) < p.length := by
    exact_mod_cast p.length_takeUntil_lt_length hv hva
  exact ((edist_le _).trans_lt h1).not_ge (hp ▸ hav)

theorem egirth_le_edist_add_edist_add_two {r a b v : V} (hab : a ≠ b)
    (ha : G.Adj a v) (hb : G.Adj b v)
    (hav : G.edist r a ≤ G.edist r v) (hbv : G.edist r b ≤ G.edist r v) :
    G.egirth ≤ G.edist r a + G.edist r b + 2 := by
  rcases eq_or_ne (G.edist r a) ⊤ with hta | hta
  · simp [hta]
  rcases eq_or_ne (G.edist r b) ⊤ with htb | htb
  · simp [htb]
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hta
  obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top htb
  have hpP : (p.concat ha).IsPath :=
    (p.isPath_of_length_eq_dist (by rw [dist, ← hp, ENat.toNat_natCast])).concat
      (notMem_support_of_length_eq_edist hp hav ha.ne.symm) ha
  have hqP : (q.concat hb).IsPath :=
    (q.isPath_of_length_eq_dist (by rw [dist, ← hq, ENat.toNat_natCast])).concat
      (notMem_support_of_length_eq_edist hq hbv hb.ne.symm) hb
  have hne : p.concat ha ≠ q.concat hb := fun h => hab (concat_inj h).1
  obtain ⟨_, -, -, c, hc, hlen⟩ := hpP.exists_isCycle_length_le_add_of_ne hqP hne
  calc G.egirth ≤ c.length := hc.egirth_le_length
    _ ≤ ((p.concat ha).length + (q.concat hb).length : ℕ) := by exact_mod_cast hlen
    _ = G.edist r a + G.edist r b + 2 := by
      simp only [length_concat, Nat.cast_add, Nat.cast_one, hp, hq]
      ring

/-!
We use this in two ways. Firstly, if `u ∈ Lᵢ₊₁` has a neighbour `w ∈ Lᵢ`, then every
other neighbour `x` of `u` lies in `Lᵢ₊₂`, as long as `2 * i + 3` is less than the
girth (otherwise `x` and `w` would be two neighbours of `u` no further from `r` than
`u`). Secondly, two distinct vertices of `Lⱼ` have no common neighbour in `Lⱼ₊₁`, as
long as `2 * j + 2` is less than the girth. (In each proof we pass from `ℕ∞` to `ℕ`
as soon as we know that the distances involved are finite.)
-/
lemma edist_eq_add_two_of_adj {r u w x : V} {i : ℕ} (hu : G.edist r u = i + 1)
    (hw : G.edist r w = i) (hwu : G.Adj w u) (hux : G.Adj u x) (hxw : x ≠ w)
    (hg : 2 * i + 3 < G.egirth) : G.edist r x = i + 2 := by
  have hx := hux.edist_le_add_one r
  rw [hu] at hx
  have := egirth_le_edist_add_edist_add_two (r := r) hxw hux.symm hwu
  lift G.edist r x to ℕ using ne_top_of_le_ne_top (by simp) hx with m
  norm_cast at hx ⊢
  by_contra hne
  have := hg.trans_le (this (by rw [hu]; norm_cast; grind)
    (by rw [hu, hw]; norm_cast; grind))
  rw [hw] at this
  norm_cast at this
  grind

lemma eq_of_adj_of_adj {r u v x : V} {j : ℕ} (hu : G.edist r u = j)
    (hv : G.edist r v = j) (hx : G.edist r x = j + 1) (hux : G.Adj u x)
    (hvx : G.Adj v x) (hg : 2 * j + 2 < G.egirth) : u = v := by
  by_contra hne
  have := egirth_le_edist_add_edist_add_two hne hux hvx (by rw [hu, hx]; simp)
    (by rw [hv, hx]; simp)
  rw [hu, hv] at this
  have := hg.trans_le this
  norm_cast at this
  grind

/-!
## The Cage Bound for Odd Girth

If the minimum degree is at least `δ + 1` and `2 * i + 4` is less than the girth,
then a vertex of `Lᵢ₊₁` has at least `δ` neighbours in `Lᵢ₊₂` (all its neighbours
except one in `Lᵢ`), and distinct vertices of `Lᵢ₊₁` have no common neighbours there.
By the second counting lemma (`mul_card_le_card_of_adj`), we have
`δ * #Lᵢ₊₁ ≤ #Lᵢ₊₂`.
-/
lemma mul_card_layer_le [Finite V] [G.LocallyFinite] {δ : ℕ}
    (h_deg : ∀ v, δ + 1 ≤ G.degree v) (r : V) {i : ℕ} (hg : 2 * i + 4 < G.egirth) :
    δ * #(G.layer r (i + 1)) ≤ #(G.layer r (i + 2)) := by
  classical
  refine mul_card_le_card_of_adj (G := G) (fun u hu => ?_)
    (fun u hu x hx v hv huv hxv => ?_)
  · obtain ⟨w, hwu, hw⟩ := exists_adj_edist_eq i (by simpa using hu)
    -- every neighbour of `u` other than `w` lies in `Lᵢ₊₂`
    have := degree_le_degIn_add_one (G.layer r (i + 2)) w
        fun x hx hxw => by
      have := edist_eq_add_two_of_adj (by simpa using hu) hw hwu hx hxw
        (hg.trans_le' (by norm_cast; grind))
      rw [mem_layer]
      exact_mod_cast this
    grind
  · simp only [mem_layer] at hu hx hv
    exact eq_of_adj_of_adj hu hx (by rw [hv]; rfl) huv hxv
      (by push_cast; convert hg using 1; ring)

/-!
By induction `#Lᵢ₊₁ ≥ (δ + 1) * δ ^ i`, provided that `2 * i + 2` is less than the
girth.
-/
lemma card_layer_ge [Finite V] [G.LocallyFinite] {δ : ℕ}
    (h_deg : ∀ v, δ + 1 ≤ G.degree v) (r : V) {i : ℕ} (hg : 2 * i + 2 < G.egirth) :
    (δ + 1) * δ ^ i ≤ #(G.layer r (i + 1)) := by
  induction i with
  | zero => simpa [layer_one] using h_deg r
  | succ i ih =>
    calc (δ + 1) * δ ^ (i + 1) = δ * ((δ + 1) * δ ^ i) := by ring
      _ ≤ δ * #(G.layer r (i + 1)) := by
          gcongr
          exact ih (hg.trans_le' (by norm_cast; grind))
      _ ≤ #(G.layer r (i + 2)) :=
          mul_card_layer_le h_deg r (by push_cast at hg; convert hg using 1; ring)

/-!
If the girth is at least `2 * k + 1` this holds for every `i < k`, and since the
layers are disjoint, `L₀, …, Lₖ` contain at least `1 + (δ + 1) * ∑ i < k, δ ^ i`
vertices. The layers around any vertex `r` already contain this many vertices, so `G`
need not be connected; we only need `V` to be nonempty. We state the girth
hypothesis with `egirth`, so it also covers acyclic graphs (whose `egirth` is `⊤`).
-/
theorem cage_bound_odd [Finite V] (G : SimpleGraph V) [G.LocallyFinite]
    [Nonempty V] (δ k : ℕ) (h_deg : ∀ v, δ + 1 ≤ G.degree v)
    (h_girth : 2 * k + 1 ≤ G.egirth) :
    1 + (δ + 1) * ∑ i ∈ range k, δ ^ i ≤ Nat.card V := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨r⟩ := ‹Nonempty V›
  calc 1 + (δ + 1) * ∑ i ∈ range k, δ ^ i
      = ∑ i ∈ range k, (δ + 1) * δ ^ i + 1 := by rw [mul_sum, add_comm]
    _ ≤ ∑ i ∈ range k, #(G.layer r (i + 1)) + #(G.layer r 0) := by
        gcongr with i hi
        · exact card_layer_ge h_deg r (h_girth.trans_lt' (by norm_cast; grind))
        · simp [layer_zero]
    _ = ∑ i ∈ range (k + 1), #(G.layer r i) :=
        (sum_range_succ' (fun i => #(G.layer r i)) k).symm
    _ = #((range (k + 1)).biUnion (G.layer r)) :=
        (card_biUnion fun i _ j _ hij => disjoint_layer hij).symm
    _ ≤ Nat.card V := Nat.card_eq_fintype_card (α := V) ▸ card_le_univ _

/-!
Informally, the cage bound holds trivially for infinite graphs, so it might seem
that the hypothesis `[Finite V]` is unnecessary. But in Lean it is essential, because
of the junk value `0` of `Nat.card` for an infinite type. For example, the infinite
path `pathNat₁` is acyclic and has minimum degree `1`, so without `[Finite V]` the
cage bound with `δ = 0` and `k = 1` would claim that `2 ≤ Nat.card ℕ = 0`.
-/

/-!
## Moore Graphs

A graph attaining the Moore bound is called a *Moore graph*. Equality forces every
layer to have the largest possible size, which (one can show) makes a Moore graph of
diameter `k` with `d ≥ 1` a `(d + 1)`-regular graph of girth `2 * k + 1`, so that it
attains the cage bound as well. (For `d = 0` the single edge `K[2]` attains the Moore
bound but has no cycles.) The simplest examples are the complete graphs: for `d ≥ 1`,
`K[d + 2]` is `(d + 1)`-regular, has diameter `1` and girth `3`, and both bounds with
`k = 1` evaluate to `d + 2`. Next come the odd cycles: `C[2 * k + 1]` is `2`-regular
(so `d = 1`), has diameter `k` (`ediam_cycleGraph`) and girth `2 * k + 1`
(`egirth_cycleGraph`), and both bounds evaluate to `2 * k + 1`.
-/
example (k : ℕ) : 1 + (1 + 1) * ∑ i ∈ Finset.range k, 1 ^ i = 2 * k + 1 := by
  simp [add_comm]

/-!
The most famous Moore graph is the Petersen graph `petersenGraph = Kn[5, 2]` of
[Kneser Graphs*](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-kneser-graphs).
It has `10` vertices, is `3`-regular, and has diameter `2` and girth `5`, so it
attains both bounds with `d = δ = 2` and `k = 2`: `10 = 1 + 3 * (1 + 2)`.

We cannot ask `decide` for the distances directly, since it cannot evaluate `edist`
([Distance Layers](https://jt496.github.io/GraphTheoryInLean/Distance/#section-distance-layers)).
Instead we reduce everything to facts about adjacency, which `decide` checks easily.
Since two `2`-subsets of `Fin 5` are adjacent iff they are disjoint, they say the
following.

* Two distinct non-adjacent vertices share one element, and the remaining two
  elements of `Fin 5` form a common neighbour.
* No three `2`-subsets of `Fin 5` are pairwise disjoint, so there are no triangles.
* Two distinct vertices have at most one common neighbour, which must be disjoint
  from their union, a set of at least three elements.
-/
lemma card_petersenGraph : Fintype.card {s : Finset (Fin 5) // s.card = 2} = 10 := by
  decide

lemma petersenGraph_isRegularOfDegree : petersenGraph.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide

lemma petersenGraph_exists_adj_adj : ∀ u v, u ≠ v → ¬ petersenGraph.Adj u v →
    ∃ w, petersenGraph.Adj u w ∧ petersenGraph.Adj w v := by
  decide

lemma petersenGraph_not_adj_of_adj_of_adj : ∀ a b c, petersenGraph.Adj a b →
    petersenGraph.Adj b c → ¬ petersenGraph.Adj a c := by
  decide

lemma petersenGraph_eq_of_adj_of_adj : ∀ x y u v, petersenGraph.Adj x u →
    petersenGraph.Adj u y → petersenGraph.Adj x v → petersenGraph.Adj v y → x ≠ y →
    u = v := by
  decide

/-!
The last fact rules out a copy `f` of `C[4]`: its vertices `f 0` and `f 2` would be
distinct with the two distinct common neighbours `f 1` and `f 3`.
-/
lemma petersenGraph_cycleGraph_four_free : C[4].Free petersenGraph := by
  rintro ⟨f⟩
  have hadj {i j : Fin 4} (h : C[4].Adj i j) : petersenGraph.Adj (f i) (f j) :=
    f.toHom.map_adj h
  have := petersenGraph_eq_of_adj_of_adj (f 0) (f 2) (f 1) (f 3) (hadj (by decide))
    (hadj (by decide)) (hadj (by decide)) (hadj (by decide))
    (fun h => absurd (f.injective h) (by decide))
  exact absurd (f.injective this) (by decide)

/-!
The diameter is at most `2` by the first fact. It is not `1`, since by the Moore
bound a `3`-regular graph of diameter `1` has at most `1 + 3 = 4` vertices.
-/
lemma ediam_petersenGraph : petersenGraph.ediam = 2 := by
  refine le_antisymm (ediam_le_of_edist_le fun u v => ?_) ?_
  · by_cases huv : u = v
    · simp [huv]
    by_cases hadj : petersenGraph.Adj u v
    · exact (edist_eq_one_iff_adj.mpr hadj).le.trans (by norm_num)
    obtain ⟨w, huw, hwv⟩ := petersenGraph_exists_adj_adj u v huv hadj
    exact (edist_le (cons huw (cons hwv nil))).trans (by simp)
  · by_contra! h
    have := moore_bound petersenGraph 2 1
      (fun v => (petersenGraph_isRegularOfDegree v).le)
      (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using h))
    rw [Nat.card_eq_fintype_card, card_petersenGraph] at this
    norm_num at this

/-!
The girth is at least `5` by `five_le_egirth`, and the pentagon
`{0, 1} — {2, 3} — {0, 4} — {1, 2} — {3, 4} — {0, 1}` shows that it is at most `5`.
-/
lemma egirth_petersenGraph : petersenGraph.egirth = 5 := by
  refine le_antisymm ?_ (five_le_egirth ?_ petersenGraph_cycleGraph_four_free)
  · let w : petersenGraph.Walk ⟨{0, 1}, rfl⟩ ⟨{0, 1}, rfl⟩ :=
      cons (v := ⟨{2, 3}, rfl⟩) (by decide) <|
      cons (v := ⟨{0, 4}, rfl⟩) (by decide) <|
      cons (v := ⟨{1, 2}, rfl⟩) (by decide) <|
      cons (v := ⟨{3, 4}, rfl⟩) (by decide) <| cons (by decide) nil
    have hw : w.IsCycle := by simp +decide [w, cons_isCycle_iff]
    simpa [w] using hw.egirth_le_length
  · intro t ht
    rw [is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    exact petersenGraph_not_adj_of_adj_of_adj a b c hab hbc hac

/-!
## The Cage Bound for Even Girth *

For even girth `2 * k` the same argument works from an edge `r — s` instead of a
vertex. Let `Aᵢ` be the set of vertices at distance `i` from `r` and `i + 1` from
`s` (so `A₀ = {r}`), and let `Bᵢ` be the same with the roles of `r` and `s`
swapped.

A vertex `u ∈ Aᵢ` has a neighbour `w` at distance `i` from `s`. If `i + 1 < k` then
all the other neighbours of `u` are at distance `i + 2` from `s` (by
`edist_eq_add_two_of_adj` with root `s`), and hence at distance `i + 1` from `r`
(since `r` and `s` are adjacent), so they lie in `Aᵢ₊₁`. Two vertices of `Aᵢ` have
no common neighbour in `Aᵢ₊₁` (by `eq_of_adj_of_adj` with root `r`). So
`δ * #Aᵢ ≤ #Aᵢ₊₁`, and by induction `#Aᵢ ≥ δ ^ i` for `i < k`.
-/
lemma mul_card_inter_layer_le [Finite V] [G.LocallyFinite] [DecidableEq V]
    {δ : ℕ} (h_deg : ∀ v, δ + 1 ≤ G.degree v) {r s : V} (hrs : G.Adj r s) {i : ℕ}
    (hg : 2 * i + 3 < G.egirth) :
    δ * #(G.layer r i ∩ G.layer s (i + 1)) ≤
      #(G.layer r (i + 1) ∩ G.layer s (i + 2)) := by
  classical
  refine mul_card_le_card_of_adj (G := G) (fun u hu => ?_)
    (fun u hu x hx v hv huv hxv => ?_)
  · simp only [mem_inter, mem_layer, Nat.cast_add, Nat.cast_one] at hu
    obtain ⟨w, hwu, hw⟩ := exists_adj_edist_eq i hu.2
    -- every neighbour of `u` other than `w` lies in `Aᵢ₊₁`
    have := degree_le_degIn_add_one
        (B := G.layer r (i + 1) ∩ G.layer s (i + 2)) (w := w) fun x hx hxw => by
      have h2 : G.edist s x = i + 2 := edist_eq_add_two_of_adj hu.2 hw hwu hx hxw hg
      have h1 : G.edist r x = i + 1 := by
        refine le_antisymm (by simpa [hu.1] using hx.edist_le_add_one r) ?_
        have := G.edist_triangle (u := s) (v := r) (w := x)
        rw [h2, edist_eq_one_iff_adj.mpr hrs.symm] at this
        rcases eq_or_ne (G.edist r x) ⊤ with h | h
        · simp [h]
        lift G.edist r x to ℕ using h with m
        norm_cast at this ⊢
        grind
      simp only [mem_inter, mem_layer]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    grind
  · simp only [mem_inter, mem_layer] at hu hx hv
    exact eq_of_adj_of_adj hu.1 hx.1 (by rw [hv.1]; push_cast; rfl) huv hxv
      (hg.trans_le' (by norm_cast; grind))

lemma pow_le_card_inter_layer [Finite V] [G.LocallyFinite] [DecidableEq V]
    {δ : ℕ} (h_deg : ∀ v, δ + 1 ≤ G.degree v) {r s : V} (hrs : G.Adj r s) {i : ℕ}
    (hg : 2 * i + 1 < G.egirth) : δ ^ i ≤ #(G.layer r i ∩ G.layer s (i + 1)) := by
  induction i with
  | zero =>
    refine card_pos.mpr ⟨r, ?_⟩
    simp [edist_eq_one_iff_adj.mpr hrs.symm]
  | succ i ih =>
    calc δ ^ (i + 1) = δ * δ ^ i := by ring
      _ ≤ δ * #(G.layer r i ∩ G.layer s (i + 1)) := by
          gcongr
          exact ih (hg.trans_le' (by norm_cast; grind))
      _ ≤ #(G.layer r (i + 1) ∩ G.layer s (i + 2)) :=
          mul_card_inter_layer_le h_deg hrs
            (by push_cast at hg; convert hg using 1; ring)

/-!
The sets `Aᵢ` and `Bⱼ` are pairwise disjoint: a vertex of `Aᵢ` is closer to `r`
than to `s`, a vertex of `Bⱼ` is closer to `s` than to `r`, and each family is
contained in the distance layers around one endpoint. So together they contain at
least `2 * ∑ i < k, δ ^ i` vertices.
-/
theorem cage_bound_even [Finite V] (G : SimpleGraph V) [G.LocallyFinite]
    [Nonempty V] (δ k : ℕ) (h_deg : ∀ v, δ + 1 ≤ G.degree v)
    (h_girth : 2 * k ≤ G.egirth) :
    2 * ∑ i ∈ range k, δ ^ i ≤ Nat.card V := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨r⟩ := ‹Nonempty V›
  obtain ⟨s, hrs⟩ := (G.degree_pos_iff_exists_adj r).mp (by have := h_deg r; grind)
  let A : ℕ → Finset V := fun i => G.layer r i ∩ G.layer s (i + 1)
  let B : ℕ → Finset V := fun i => G.layer s i ∩ G.layer r (i + 1)
  have hdisj : ∀ i j (v : V), v ∈ A i ∪ B i → v ∈ A j ∪ B j → i = j := by
    intro i j v hi hj
    simp only [A, B, mem_union, mem_inter, mem_layer] at hi hj
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp_all <;> norm_cast at * <;> grind
  have hAB : ∀ i, Disjoint (A i) (B i) := fun i =>
    Finset.disjoint_left.mpr fun v hA hB => by
      simp only [A, B, mem_inter, mem_layer] at hA hB
      rw [hA.1] at hB
      norm_cast at hB
      grind
  calc 2 * ∑ i ∈ range k, δ ^ i = ∑ i ∈ range k, (δ ^ i + δ ^ i) := by
        rw [sum_add_distrib, two_mul]
    _ ≤ ∑ i ∈ range k, (#(A i) + #(B i)) := by
        gcongr with i hi <;> have := mem_range.mp hi
        · exact pow_le_card_inter_layer h_deg hrs
            (h_girth.trans_lt' (by norm_cast; grind))
        · exact pow_le_card_inter_layer h_deg hrs.symm
            (h_girth.trans_lt' (by norm_cast; grind))
    _ = ∑ i ∈ range k, #(A i ∪ B i) :=
        sum_congr rfl fun i _ => (card_union_of_disjoint (hAB i)).symm
    _ = #((range k).biUnion fun i => A i ∪ B i) := by
        refine (card_biUnion fun i _ j _ hij => ?_).symm
        rw [Function.onFun, Finset.disjoint_left]
        exact fun v hi hj => hij (hdisj i j v hi hj)
    _ ≤ Nat.card V := Nat.card_eq_fintype_card (α := V) ▸ card_le_univ _

/-!
The even bound gives a second proof that the Petersen graph has girth at most `5`,
without exhibiting a cycle: a `3`-regular graph of girth at least `6` would have at
least `2 * (1 + 2 + 4) = 14` vertices.
-/
example : petersenGraph.egirth ≤ 5 := by
  by_contra! h
  have : Nonempty {s : Finset (Fin 5) // s.card = 2} := ⟨⟨{0, 1}, by decide⟩⟩
  have := cage_bound_even petersenGraph 2 3
    (fun v => (petersenGraph_isRegularOfDegree v).ge)
    ((by norm_num : (2 * 3 : ℕ∞) ≤ 5 + 1).trans (Order.add_one_le_of_lt h))
  rw [Nat.card_eq_fintype_card, card_petersenGraph] at this
  norm_num [Finset.sum_range_succ] at this

/-!
The complete bipartite graphs attain the even cage bound with `k = 2`. For `δ ≥ 1`,
`K[δ + 1, δ + 1]` is `(δ + 1)`-regular, has girth `4`
(`egirth_completeBipartiteGraph`), and has `2 * (1 + δ)` vertices. (For `δ = 0` it
is a single edge, which is acyclic.)
-/
example (δ : ℕ) :
    Nat.card (Fin (δ + 1) ⊕ Fin (δ + 1)) = 2 * ∑ i ∈ Finset.range 2, δ ^ i := by
  simp [two_mul]

/-!
# Albertson's Precolouring Extension Theorem

Albertson's precolouring extension theorem says that if `G` is `k`-colourable and `s`
is a set of vertices that are pairwise at distance at least `4`, then any assignment
`f : s → Fin (k + 1)` of colours to the vertices of `s` extends to a proper
`(k + 1)`-colouring of `G`. (In general a *precolouring* must be a proper colouring
of the subgraph induced by `s`, but here no two vertices of `s` are adjacent, so
every assignment of colours is allowed.)

The hypothesis is stated with `edist`. Had we written `4 ≤ G.dist u w` instead, the
junk value `0` for unreachable pairs would forbid precoloured vertices in different
components, giving a strictly weaker theorem.

Take any `k`-colouring `c` of `G`, so the extra colour `Fin.last k` is unused. Build
the extension `c'` by recolouring only near `s`: every `w ∈ s` gets its target colour
`f w`, and whenever `f w` is one of the original `k` colours, each neighbour of `w`
that already used that colour is swapped to the spare colour `Fin.last k`. The
distance hypothesis guarantees that the recoloured neighbourhoods of distinct
vertices of `s` are non-adjacent (any edge between them would give a walk of length
`≤ 3` between two vertices of `s`), so no new monochromatic edge is created.
-/
theorem Colorable.extend_precoloring {k : ℕ} (hk : G.Colorable k) {s : Set V}
    (hs : s.Pairwise fun u w ↦ 4 ≤ G.edist u w) (f : s → Fin (k + 1)) :
    ∃ C : G.Coloring (Fin (k + 1)), ∀ w : s, C w = f w := by
  classical
  obtain ⟨c⟩ := hk
  -- Two vertices of `s` joined by a walk of length at most `3` are equal.
  have close {a b : V} (ha : a ∈ s) (hb : b ∈ s) (p : G.Walk a b)
      (hp : p.length ≤ 3) : a = b := by
    by_contra hne
    have := (hs ha hb hne).trans (edist_le p)
    norm_cast at this
    grind
  -- `v` is *pushed* if a neighbour in `s` wants its colour.
  let P (v : V) : Prop := ∃ w : s, G.Adj w v ∧ f w = (c v).castSucc
  let c' : V → Fin (k + 1) := fun v ↦
    if hv : v ∈ s then f ⟨v, hv⟩ else if P v then Fin.last k else (c v).castSucc
  -- A precoloured vertex never clashes with a neighbour outside `s`.
  have aux {a b : V} (ha : a ∈ s) (hb : b ∉ s) (hab : G.Adj a b) : c' a ≠ c' b := by
    simp only [c', ha, hb, ↓reduceDIte]
    split_ifs with hP
    · obtain ⟨w, hwb, hw⟩ := hP
      obtain rfl : w = ⟨a, ha⟩ :=
        Subtype.ext (close w.2 ha (cons hwb (cons hab.symm nil)) (by simp))
      rw [hw]
      exact Fin.castSucc_ne_last _
    · exact fun h => hP ⟨⟨a, ha⟩, hab, h⟩
  refine ⟨Coloring.mk c' fun {x y} hxy => ?_, fun w => by
    change c' w = f w
    simp [c']⟩
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · exact absurd (close hx hy (cons hxy nil) (by simp)) hxy.ne
  · exact aux hx hy hxy
  · exact (aux hy hx hxy.symm).symm
  · simp only [c', hx, hy, ↓reduceDIte]
    split_ifs with hPx hPy hPy
    · -- both pushed by the same vertex of `s`, so `c x = c y`
      obtain ⟨wx, hwx, hfx⟩ := hPx
      obtain ⟨wy, hwy, hfy⟩ := hPy
      obtain rfl : wx = wy := Subtype.ext
        (close wx.2 wy.2 (cons hwx (cons hxy (cons hwy.symm nil))) (by simp))
      exact absurd (Fin.castSucc_injective _ (hfx.symm.trans hfy)) (c.valid hxy)
    · exact (Fin.castSucc_ne_last _).symm
    · exact Fin.castSucc_ne_last _
    · exact fun h => c.valid hxy (Fin.castSucc_injective _ h)

/-!
Distance `4` cannot be replaced by `3`. Take `K[3, 3]` and attach a pendant vertex to
each of its six vertices; the pendants are pairwise at distance at least `3`. On each
side, colour the three pendants `0`, `1` and `2`, so the vertices on that side can
only use the colours `{1, 2}`, `{0, 2}` and `{0, 1}` respectively. No colour is
available to all three, so each side needs at least two colours; but the two sides of
`K[3, 3]` need disjoint sets of colours, which is impossible with three colours. The
graph is bipartite, so this precolouring of a `2`-colourable graph does not extend
to a `3`-colouring.
-/

end SimpleGraph
