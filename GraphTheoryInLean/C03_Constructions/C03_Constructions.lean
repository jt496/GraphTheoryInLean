/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.Common
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.InformationTheory.Hamming
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.FieldTheory.Finite.GaloisField
namespace SimpleGraph
/-!
In this chapter we will introduce some of the concrete examples of simple graphs that
can be found in Mathlib together with a few new ones. The idea is to give a flavour
of the kinds of constructions that are possible in Mathlib. It also offers a good
excuse to introduce many of the fundamental types that may be unfamiliar to graph
theorists but are used throughout Mathlib. These include `Bool`, `Fin`, `Option`,
`Prod`, `Sigma`, `Subtype`, `Sum` and `Unit`.

Two of the constructions we introduce below, the
[hypercube](#section-hypercube) and
[Mycielskian](#section-mycielskian), will serve as running examples throughout
the remaining chapters.

Beware that in this chapter we are looking at *constructions*, and so we will see
examples of complete bipartite graphs and cycle graphs etc., but we won't see any
discussion yet of what it means for a graph to *be* bipartite or to *contain* a cycle
etc.

To sanity-check our definitions, we will want to perform computations on small
examples using `#eval` and `decide`. We will look at such computations in much more
detail in the next chapter, but for them to work we need to provide decidability
instances for adjacency in the graphs we define. Feel free to ignore these and
revisit them once you have read the next chapter!


# Basic Families of Graphs

We start with the most basic families of graphs: complete and empty graphs, single
edges, paths, cycles and complete bipartite graphs.

## Complete and Empty Graphs

Given a vertex set `V` the *complete* graph on `V` has all possible edges while the
*empty* graph on `V` has no edges.

In Mathlib these are usually referred to by their roles as the top `⊤` and bottom `⊥`
elements of the complete atomic Boolean algebra formed by `SimpleGraph V` (see
[Order](#section-order) for more details).
-/
#source completeGraph
#source emptyGraph
/-!
As we saw in [Top and Bottom](#section-top-and-bottom), results about these graphs
use the `top` and `bot` names, as in `top_adj` and `bot_adj`.

[Figure: The complete graphs $K_3$ and $K_5$](https://jt496.github.io/GraphTheoryInLean/figures/complete.svg)

Recall that `Fin n` is the type of natural numbers less than `n` with addition mod
`n`. (In particular `Fin 0` is the empty type.)

We can construct the complete graph on `Fin n` as follows.
-/
example (n : ℕ) : SimpleGraph (Fin n) := completeGraph (Fin n)

/-!
We can introduce the notation `K[n]` for the complete graph on `Fin n` as follows.
(The keyword `scoped` makes the notation available only inside
`namespace SimpleGraph`, or wherever `SimpleGraph` is opened.)
-/
/-- The complete graph on `Fin n` is denoted `K[n]`. -/
scoped notation "K[" n "]" => completeGraph (Fin n)
/-!
Since `Fin n` has decidable equality, `K[n]` has decidable adjacency: if we have a
procedure for deciding whether two vertices are equal then we can decide whether
they are adjacent in the complete graph, since adjacency is simply not-equal-to `≠`.

For example, `10` and `111` are adjacent in `K[417]`.
-/
example : K[417].Adj 10 111 := by decide
/-!
We can similarly introduce the notation `E[n]` for the empty graph on `Fin n`.
-/
/-- The empty graph on `Fin n` is denoted `E[n]`. -/
scoped notation "E[" n "]" => emptyGraph (Fin n)

/-!
## A Single Edge

We can construct a `SimpleGraph V` with just one edge between two vertices `s : V`
and `t : V` using `edge s t`. If `s = t` then this is just the empty graph on
`V`. (Recall that `SimpleGraph V` is a `CompleteAtomicBooleanAlgebra`: for `s ≠ t`
these graphs are the atoms of the algebra.)
-/
#source edge  -- def edge : SimpleGraph V := fromEdgeSet {s(s, t)}
/-!
You may wonder why we care about the graph with a single edge, but in fact it can be
very useful. Arguments about adding a single edge to, or removing one from, a graph
can be formulated using it.

For example, if we add `edge s t` to `G`, where `s` and `t` are distinct vertices
that do not form an edge in `G`, then we get a strictly larger graph.
-/
#check lt_sup_edge -- .. (hne : s ≠ t) (hn : ¬G.Adj s t) : G < G ⊔ edge s t

/-!
## Path Graphs

In Mathlib the canonical path graph on `n` vertices is constructed as the Hasse
diagram of the linear order on `Fin n`, so we first describe Hasse diagrams.

Given a poset `(P, ≤)` we say that `a ∈ P` is *covered by* `b ∈ P` if `a < b` and
`∀ c ∈ P, a < c → ¬ c < b`. In Mathlib this is denoted `a ⋖ b`.

The *Hasse diagram* of a poset `(P, ≤)` is the graph with vertex set `P` and edges
between pairs of vertices such that one is covered by the other.

[Figure: The Hasse diagram of the divisors poset of 60](https://jt496.github.io/GraphTheoryInLean/figures/hasse.svg)
-/

example {P : Type*} {u v : P} [PartialOrder P] :
    (hasse P).Adj u v ↔ u ⋖ v ∨ v ⋖ u := by rfl

/-!
The path graph on `n` vertices is then the Hasse diagram of `Fin n`. Recall that
addition in `Fin n` is defined mod `n`.
-/
example : (2 : Fin 4) + 2 = 0 := rfl

/-!
So when describing adjacency in this graph we need to use the underlying `ℕ` values.
-/
#source pathGraph
example (n : ℕ) (a b : Fin n) :
    (pathGraph n).Adj a b ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val := pathGraph_adj

/-!
[Figure: The path graphs $P_2$, $P_4$ and $P_7$](https://jt496.github.io/GraphTheoryInLean/figures/paths.svg)


We introduce the notation `P[n]` for path graphs as follows:
-/
@[inherit_doc pathGraph]
scoped notation "P[" n "]" => pathGraph n

/-!
Mathlib has no decidability instance for adjacency in `hasse` or `pathGraph`, so we
will need to provide our own if we want to do computations with these graphs. This
is a bit more work than the instances we give in this chapter, so we defer it until
[Decidability, Finiteness and Degrees](#chapter-decidability-finiteness-and-degrees).

## Cycle Graphs

For any `n : ℕ` we can define the *cycle graph* on `n` vertices as the graph with
vertex set `Fin n` and edges between vertices that differ by `1` modulo `n`. Although
we usually think of cycles as always containing at least 3 vertices, in Mathlib we
also have cycle graphs on 0, 1, and 2 vertices. This is a common pattern in Mathlib:
rather than add side conditions to the definition, we will instead need to check when
using `cycleGraph` whether or not it is in fact a cycle!

For `3 ≤ n` the definition of adjacency is obvious:
`Adj a b := a - b = 1 ∨ b - a = 1`. This also makes sense for `n = 2` but gives us
the graph on `Fin 2` with a single edge.

The cases `n = 0` and `n = 1` need a bit more care: for `a b : Fin 0` we can't
write `a - b = 1 ∨ b - a = 1` since there is no `1 : Fin 0`. While for `a b : Fin 1`
we can write `a - b = 1 ∨ b - a = 1` but `1 = 0` in `Fin 1` so this would define a
graph with loops, which is not allowed.
-/
example : (1 : Fin 1) = 0 := rfl
/-!
The solution is to define `cycleGraph n` to be the empty graph for `n = 0` and
`n = 1`.
-/
#source cycleGraph --  def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
                   --    | 0 | 1 => ⊥
                   --    | _ + 2 => {
                   --      Adj a b := a - b = 1 ∨ b - a = 1
                   --    }
/-!
[Figure: The cycle graphs $C_3$ and $C_6$](https://jt496.github.io/GraphTheoryInLean/figures/cycles.svg)

We introduce the notation `C[n]` for cycle graphs.
-/
@[inherit_doc cycleGraph]
scoped notation "C[" n "]" => cycleGraph n

#check C[5]   -- C[5] : SimpleGraph (Fin 5)
example : C[5].Adj 0 1 := by decide
example : ¬ C[5].Adj 4 2 := by decide

/-!
As we saw above, for `n = 0` and `n = 1`, `C[n]` is the empty graph on `Fin n`, while
for `n = 2` it is the complete graph `K[2]`. The first two of these are
*definitional* equalities (in the sense of [Definitional and Propositional
Equalities](#section-definitional-and-propositional-equalities)), while the last is
not. `C[2].Adj a b` is `a - b = 1 ∨ b - a = 1` while `K[2].Adj a b` is `a ≠ b`. We
can prove that these are equivalent, but they are not definitionally equal.
-/
example : C[0] = E[0] := rfl
example : C[1] = E[1] := rfl
example : C[2] = K[2] := cycleGraph_two_eq_top

/-!
## Complete Bipartite Graphs

Given two disjoint vertex sets `V` and `W` we can form the *complete bipartite* graph
with classes `V` and `W`. This seems to involve the idea that `V` and `W` are
disjoint, but in Lean we are working with types not sets and so have no way of
talking about *disjointness* of two arbitrary types.

Lean does however have the very useful `Sum` type, written `V ⊕ W`, which plays the
role of the disjoint union of types `V` and `W`. Note that this is not the same as
the set-theoretic union: any `x : V ⊕ W` "knows" which of the two sides of the sum it
came from. It is either `Sum.inl v` for some `v : V`, or `Sum.inr w` for some
`w : W`. In particular we can form the disjoint union of a type `V` with itself as
`V ⊕ V`.
-/
#source Sum
example {V : Type*} (v : V) : V ⊕ V := Sum.inl v

/-!
This gives a natural way to define *complete bipartite* graphs.
-/
#source completeBipartiteGraph
/-!
[Figure: The complete bipartite graph $K_{4,5}$](https://jt496.github.io/GraphTheoryInLean/figures/completebipartite.svg)

We introduce the notation `K[s, t]` for the canonical complete bipartite graph with
parts `Fin s` and `Fin t`.
-/
/-- The complete bipartite graph on `Fin s ⊕ Fin t` is denoted `K[s, t]`. -/
scoped notation "K[" s ", " t "]" => completeBipartiteGraph (Fin s) (Fin t)

#check K[4, 5]  -- K[4, 5] : SimpleGraph (Fin 4 ⊕ Fin 5)

/-!
If we try to check adjacency of two vertices in `K[4, 5]` we get an error. (The
actual error is suppressed in the Lean source file by the `#guard_msgs` command and
only shown in the HTML version. Delete the `#guard_msgs` line to see the error
message in VS Code.)
-/
/-- error: failed to synthesize
  Decidable (K[4, 5].Adj (Sum.inl 0) (Sum.inr 3)) -/
#guard_msgs (substring := true) in
#eval K[4, 5].Adj (Sum.inl 0) (Sum.inr 3)

/-!
This is because, as for `pathGraph`, there is no decidability instance for
`completeBipartiteGraph` in Mathlib. This time, though, it is easy to provide the
missing instance ourselves. (Don't worry if this is unfamiliar; we will look at
decidability in *much* more detail in [Decidability, Finiteness and
Degrees](#chapter-decidability-finiteness-and-degrees).)
-/
instance (V W : Type*) : DecidableRel (completeBipartiteGraph V W).Adj :=
    fun v w => by
  unfold completeBipartiteGraph
  infer_instance

example : K[4, 5].Adj (Sum.inl 0) (Sum.inr 3) := by decide

/-!
# Algebraic Constructions

Next we look at two families of graphs whose vertices are the elements of a group,
with adjacency defined using the group operation.

## Circulant Graphs

If `G` is an additive group and `s ⊆ G`, the associated *circulant graph* has vertex
set `G` with edges between vertices whose difference belongs to `s` (suitably
symmetrized so that the resulting graph is undirected and without loops).
-/

#source circulantGraph -- def circulantGraph {G : Type*} [AddGroup G] (s : Set G) :
                       --        SimpleGraph G := fromRel (· - · ∈ s)

example : SimpleGraph (Fin 8) := circulantGraph ({1, 3} : Set (Fin 8))

/-!
[Figure: The circulant graph on $\mathbb{Z}_8$ with differences 1 and 3](https://jt496.github.io/GraphTheoryInLean/figures/circulant.svg)
-/
/-!
### Paley Graphs

A special case of a circulant graph is the Paley graph. If `F` is a finite field, the
*Paley graph*
[Paley 1933](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-paley-1933)
of `F` is the circulant graph on `F` whose differences are the nonzero squares in
`F`. Usually one also requires `|F| ≡ 1 mod 4`: then `-1` is a square, so `u - v` is
a square if and only if `v - u` is, and each vertex is adjacent to exactly half of
the others. (For any other finite field the definition below gives the complete
graph: if `|F| ≡ 3 mod 4` then exactly one of `d` and `-d` is a square for each
`d ≠ 0`, while if `|F|` is even then every element of `F` is a square.) The
`circulantGraph` calls the constructor `fromRel (· - · ∈ s)`, which automatically
removes loops and symmetrizes the relation, so we can simply take all the squares,
including `0`.
-/
/-- The Paley graph of a field `F`: distinct elements are adjacent if their
difference is a square. -/
abbrev paleyGraph (F : Type*) [Field F] : SimpleGraph F :=
  circulantGraph {y | IsSquare y}

/-!
Mathlib's type of integers modulo `n` is `ZMod n`. (For `n ≠ 0` it is defined to be
`Fin n`.) If `p` is prime then `ZMod p` is a field, so `paleyGraph (ZMod p)` is the
Paley graph on `p` vertices. However, Lean will only find the `Field (ZMod p)`
instance if it can find a proof that `p` is prime, in the form of an instance of
`Fact (Nat.Prime p)`. Mathlib provides these for `p = 2` and `p = 3`, but for
`p = 17` we need to supply one ourselves.
-/
instance fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by decide⟩

#source ZMod
example : SimpleGraph (ZMod 17) := paleyGraph (ZMod 17)

/-!
[Figure: The Paley graph $P(17)$](https://jt496.github.io/GraphTheoryInLean/figures/paleyGraph.svg)

## Cayley Graphs

Cayley graphs
[Cayley 1878](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-cayley-1878)
are also defined in Mathlib. They are defined for any vertex type with a
multiplication or addition operation, not just for groups.

If you look at the definition you will see the use of the `@[to_additive]` attribute
to give both multiplicative and additive versions of the same construction. (In
particular if you look for the source code for `addCayley`, you will be taken to
`mulCayley`.)
-/
#source mulCayley
/-!
The symmetric group on four points is `Equiv.Perm (Fin 4)` in Mathlib, and its
elements can be written in cycle notation using `c[...]`. Taking a `3`-cycle and a
`4`-cycle as generators gives the graph drawn below.
-/

/-- The Cayley graph of the symmetric group on `Fin 4` generated by a `3`-cycle and a
`4`-cycle. -/
abbrev cayleyS4 : SimpleGraph (Equiv.Perm (Fin 4)) :=
  mulCayley {c[0, 1, 2], c[0, 1, 2, 3]}

/-!
It has one vertex for each of the 24 permutations and is `4`-regular, since each
generator accounts for two of the edges at every vertex: one to the neighbour it
multiplies to, and one back from its inverse.
-/
#eval Fintype.card (Equiv.Perm (Fin 4)) -- 24
#eval cayleyS4.degree 1 -- 4
#eval cayleyS4.edgeFinset.card -- 48

/-!
The two edge colours in the figure are the two generators: the triangles are the
edges contributed by the `3`-cycle and the squares those contributed by the
`4`-cycle. Splitting the graph up like this is exactly `mulCayley_union`, which says
that a union of generating sets gives the union of the corresponding Cayley graphs.
-/
example : cayleyS4 = mulCayley {c[0, 1, 2]} ⊔ mulCayley {c[0, 1, 2, 3]} := by
  rw [← mulCayley_union, Set.singleton_union]

/-!
[Figure: The Cayley graph of $S_4$ generated by a 3-cycle and a 4-cycle](https://jt496.github.io/GraphTheoryInLean/figures/cayley.svg)
-/
/-!
# Operations on Graphs

So far each construction has built a graph from scratch. We now look at some ways
of building new graphs from old ones.

## Line Graphs

Given `G : SimpleGraph V`, its *line graph* is the graph whose vertices are the edges
of `G`, in which two distinct edges are adjacent iff they share a vertex. In Mathlib
this is defined as follows.
-/
#source lineGraph -- def lineGraph : SimpleGraph G.edgeSet where
                  --    Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
                  --    symm.symm e₁ e₂ hadj := by rwa [ne_comm, Set.inter_comm]

/-!
We introduce the notation `L[G]` for the line graph of `G`.
-/
@[inherit_doc lineGraph]
scoped notation "L[" G "]" => lineGraph G
/-!
The edge set `G.edgeSet` is a `Set (Sym2 V)`, so to use it as the vertex type of
`L[G]`, Lean coerces it to the subtype `{e : Sym2 V // e ∈ G.edgeSet}`, written
`↑G.edgeSet`. A vertex of `L[G]` is therefore an edge bundled with a proof that it
belongs to `G`: a term `⟨s(u, v), h⟩` with `h : s(u, v) ∈ G.edgeSet`. This membership
is the same as `G.Adj u v` (`mem_edgeSet`). For a concrete graph, `decide` can supply
`h`.
-/
#check L[K[4]] -- SimpleGraph ↑K[4].edgeSet
#check (⟨s(0, 1), by decide⟩ : K[4].edgeSet)
/-!
Adjacency in `L[G]` has two parts. The condition `e₁ ≠ e₂` is needed because every
edge shares a vertex with itself, and simple graphs have no loops. The condition
`(e₁ ∩ e₂ : Set V).Nonempty` says that the edges share a vertex. To state it, each
edge is coerced twice: first from `↑G.edgeSet` to `Sym2 V`, and then from `Sym2 V` to
`Set V`, the set of its endpoints.

For example, `s(0, 1)` and `s(0, 2)` are adjacent in `L[K[4]]`. After
`constructor`, the first goal says that they are distinct and the second that they
share a vertex, for which `0` is a witness.

[Figure: Left: $K_4$. Right: its line graph, the octahedron](https://jt496.github.io/GraphTheoryInLean/figures/lineGraph.svg)
-/
example : L[K[4]].Adj ⟨s(0, 1), by decide⟩ ⟨s(0, 2), by decide⟩ := by
  constructor
  · grind
  · -- After the double coercion we need to check that the `Set (Fin 4)`
    -- `{0, 1}` and `{0, 2}` have nonempty intersection.
    -- ⊢ (↑↑⟨s(0, 1), ⋯⟩ ∩ ↑↑⟨s(0, 2), ⋯⟩).Nonempty
    use 0; simp

/-!
## Box Products

The *box product* of two graphs `G` and `H` is the graph on the Cartesian product of
their vertex sets, where a pair of vertices `(g₁, h₁)` and `(g₂, h₂)` are adjacent if
either `g₁ = g₂` and `H.Adj h₁ h₂` or `h₁ = h₂` and `G.Adj g₁ g₂`. This is written
`G □ H` in Mathlib. Its vertex type is the product type `V × W`, whose elements are
pairs `(g, h)`; for `x : V × W` the two components are `x.1` and `x.2` (also written
`x.fst` and `x.snd`). For each vertex `h` of `H`, the vertices `(g, h)` span a copy
of `G` in `G □ H`, the *`G`-fibre* at `h`; similarly each vertex `g` of `G` gives a
copy of `H`, the *`H`-fibre* at `g`.

[Figure: The box product of $P_3$ and $K_3$](https://jt496.github.io/GraphTheoryInLean/figures/boxprod.svg)
-/
#source boxProd
/-!
Adjacency in the box product of a path and a cycle. (We use `n + 2` because
Mathlib's `cycleGraph_adj` is stated for `cycleGraph (n + 2)`; the more awkward
`cycleGraph_adj'` covers every `n`.)
-/
example {n : ℕ} {a b c d : Fin (n + 2)} : (P[n + 2] □ C[n + 2]).Adj (a, b) (c, d) ↔
    ((a.val + 1 = c.val ∨ c.val + 1 = a.val) ∧ b = d) ∨
        ((b - d = 1 ∨ d - b = 1) ∧ a = c) := by
  simp [pathGraph_adj, cycleGraph_adj]

/-!
## Sum and Sigma Graphs *

Given graphs `G : SimpleGraph V` and `H : SimpleGraph W`, their *(disjoint) sum*
`G ⊕g H` is the graph formed by placing a copy of `G` and a copy of `H` side by
side, with no edges between them. Its vertex type is the sum type `V ⊕ W`, whose
elements are either `Sum.inl v` with `v : V` or `Sum.inr w` with `w : W`. Two
vertices `Sum.inl v₁` and `Sum.inl v₂` are adjacent iff `G.Adj v₁ v₂`, two
vertices `Sum.inr w₁` and `Sum.inr w₂` are adjacent iff `H.Adj w₁ w₂`, and no
vertex `Sum.inl v` is adjacent to any vertex `Sum.inr w`. Mathlib defines `G ⊕g H`
by pattern matching on these cases.
-/
#source SimpleGraph.sum
#check sum_adj_inl
#check sum_adj_inr

/-!
More generally, we can take the disjoint union of an indexed family of graphs, which
we call a *sigma graph*. This is not currently in Mathlib, so we define it here. If
the graph indexed by `i : ι` has vertex type `V i`, then the vertex type of the
disjoint union is the *dependent pair* (or `Sigma`) type `Σ i, V i`.
-/
#source Sigma
/-!
A vertex of `Σ i, V i` is a pair `⟨i, u⟩` consisting of an index `i : ι` and an
element `u : V i`. The pair is called *dependent* because the type of its second
component depends on the value of its first. Lean prints `Σ i, V i` as
`(i : ι) × V i`, so expect to see that form in goals and `#check` output.

Two vertices `⟨i, u⟩` and `⟨j, v⟩` should be adjacent iff `i = j` and `u` and `v`
are adjacent in `G i`. Stating this takes some care: `u : V i` but `v : V j`, so
`(G i).Adj u v` does not type-check. A proof `h : i = j` does not fix this on its
own, because Lean only identifies types that are equal by definition, and `V i` and
`V j` are not. Instead we use `h` to cast `v` along the equation, giving
`h ▸ v : V i`.

We mark the definition `protected`, so that even inside `namespace SimpleGraph` it
must be called `SimpleGraph.sigma` (or `Σg`). This stops the short name `sigma` from
clashing with other functions of that name, such as `Finset.sigma`.
-/
/-- The disjoint union of an indexed family of graphs. Given an index type `ι` and,
for each `i : ι`, a graph `G i` on the vertex type `V i`, the disjoint union `Σg G`
has vertex type `Σ i, V i`, and two vertices are adjacent iff they lie in the same
graph `G i` and are adjacent there. -/
@[simps!]
protected def sigma {ι : Type*} {V : ι → Type*} (G : (i : ι) → SimpleGraph (V i)) :
    SimpleGraph (Σ i, V i) where
  Adj := fun ⟨i, u⟩ ⟨j, v⟩ => ∃ h : i = j, (G i).Adj u (h ▸ v)
  symm := by
    constructor
    rintro ⟨i, u⟩ ⟨j, v⟩ ⟨rfl, hadj⟩
    exact ⟨rfl, hadj.symm⟩
/-!
In the proof of `symm` above, `rintro ⟨i, u⟩ ⟨j, v⟩ ⟨rfl, hadj⟩` introduces the two
vertices and splits the adjacency proof into its two parts. The pattern `rfl`
substitutes `i = j` everywhere, after which `h ▸ v` reduces to `v`.

The substitution is needed because the cast `h ▸ v` only computes (in the sense of
[Definitional and Propositional
Equalities](#section-definitional-and-propositional-equalities)) when both sides of
`h` are definitionally equal, in which case it reduces to `v`. While `i` and `j` are
distinct variables the cast is stuck, just like `0 + n`, and no amount of unfolding
gets past it to `v`. We will meet this issue again in [Decidability and Kernel
Reduction*](#section-decidability-and-kernel-reduction) and when we need to change
the endpoints of walks in [Copy](#section-copy).

The `@[simps!]` attribute generates `sigma_adj`, in which the `⋯` hides the proof
of `i = j` used by `▸`. We write `Σg G` for `SimpleGraph.sigma G`.
-/
#check SimpleGraph.sigma_adj

@[inherit_doc] scoped prefix:60 "Σg " => SimpleGraph.sigma

/-- The disjoint union of the complete graphs `K[0]`, `K[1]`, `K[2]`, …. -/
abbrev natDisjointComplete : SimpleGraph (Σ i, Fin i) :=
  Σg (fun (i : ℕ) => K[i])

/-!
In our next example we show that two vertices `⟨i, a⟩` and `⟨j, b⟩` of
`natDisjointComplete` are adjacent iff they lie in the same complete graph (`i = j`)
and are distinct. We cannot write `a ≠ b` here, since `a : Fin i` and `b : Fin j`
have different types; this is the same problem as above. Comparing the underlying
natural numbers `(a : ℕ)` and `(b : ℕ)` avoids it.

In the proof, `t₁ <;> t₂` runs the tactic `t₂` on every goal produced by `t₁`: here
`constructor` splits the `↔` into two implications, and `rintro ⟨rfl, h⟩` then
introduces the hypotheses in both, substituting as in the `sigma` proof above.
-/
example {i j : ℕ} {a : Fin i} {b : Fin j} :
    natDisjointComplete.Adj ⟨i, a⟩ ⟨j, b⟩ ↔ i = j ∧ (a : ℕ) ≠ b := by
  constructor <;> rintro ⟨rfl, h⟩
  · exact ⟨rfl, Fin.val_ne_of_ne h⟩
  · exact ⟨rfl, fun hab => h (congrArg Fin.val hab)⟩

/-!
# Hypercube

Often there is more than one way to construct a particular graph. A good example of
this is the `n`-*dimensional hypercube*, which can be constructed in many different
ways: as the Hasse diagram of the Boolean algebra of subsets of an `n`-element set;
as the graph on `Fin n → Bool` with edges between vertices that differ in exactly one
coordinate (i.e. at Hamming distance one
[Hamming 1950](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-hamming-1950));
or as the box product of `n` copies of `K₂`.

The Hasse diagram construction is very easy to give, but then is a pain to work with.
-/
/-- The Hasse diagram construction of the `n`-dimensional hypercube. -/
abbrev hypercubeHasse (n : ℕ) : SimpleGraph (Finset (Fin n)) :=
  hasse _

/-!
The Hamming cube construction is also easy to give and easier to work with than the
Hasse diagram.
-/
/-- The Hamming cube definition of the `n`-dimensional hypercube. -/
def hypercubeHamming (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1
  symm := ⟨by simp [hammingDist_comm]⟩

/-!
But for our purposes the most useful construction of the hypercube is as the box
product of `n` copies of `K₂`.

The box product construction of the hypercube requires a bit more setup, but will be
worth it. The reason we choose this construction is that it is *recursive* in `n`:
its vertex type is built so that `Q[n + 1] = Q[n] □ K₂` holds definitionally. Almost
every result we prove about the hypercube in the later chapters is by induction on
`n`, and this recursive structure is exactly what allows these to work. It
also lets us reuse Mathlib's box product lemmas directly.

For the box product construction we need to first define the vertex type of the
hypercube. There are two things we need to decide: firstly what should the vertex
type of `Q[0]` be? Since `Q[0]` is a single vertex we will use the canonical type
with exactly one element, `Unit`.
-/
#check Unit
/-!
Secondly, when we said `Q[n + 1] = Q[n] □ K₂` we need to choose a vertex type for
`K₂`. We will choose the type `Bool` with its two elements, `false` and `true`.
-/
#source Bool

/-- The vertex type of the `n`-dimensional hypercube (box product construction). -/
@[implicit_reducible]
def HypercubeVert : ℕ → Type
  | 0 => Unit                       -- The canonical type with exactly one element
  | n + 1 => HypercubeVert n × Bool -- The previous vertex type times `Bool`

/-!
(Note that `HypercubeVert n` is really just `Fin n → Bool` but defined so that the
recursion holds definitionally. We can still easily take the Hamming distance
viewpoint and we will equip it with the Hamming distance when needed in
[Hamming Paths](#section-hamming-paths).)

The `@[implicit_reducible]` attribute lets Lean unfold `HypercubeVert (n + 1)` to
`HypercubeVert n × Bool` when it checks that implicit arguments have the expected
type (as `simp` does before rewriting), while keeping `HypercubeVert` opaque to
instance search so that the instances we provide for `HypercubeVert n` in
[Computations with Hypercubes](#section-computations-with-hypercubes) are still
found.
-/
@[simp]
lemma hypercubeVert_zero : HypercubeVert 0 = Unit := rfl

lemma hypercubeVert_succ (n : ℕ) :
    HypercubeVert (n + 1) = (HypercubeVert n × Bool) := rfl

/-!
The `n`-dimensional hypercube can now be defined recursively as the box product of
the previous hypercube with `K₂`, the complete graph on two vertices (where `Bool` is
the vertex type of `K₂`).
-/

/-- The `n`-dimensional hypercube defined as the box product of `n` copies of `K₂`.
-/
def hypercube : (n : ℕ) → SimpleGraph (HypercubeVert n)
    -- The empty graph on one vertex
  | 0 => ⊥
    -- The box product of the `n`-hypercube with `K₂` on `Bool`
  | n + 1 => (hypercube n).boxProd ⊤

/-!
We will use `Q[n]` as notation for the `n`-dimensional hypercube.

[Figure: The 4-dimensional hypercube $Q_4$](https://jt496.github.io/GraphTheoryInLean/figures/hypercube.svg)
-/
@[inherit_doc hypercube]
scoped notation "Q[" n "]" => hypercube n

@[simp]
lemma hypercube_zero : Q[0] = ⊥ := rfl

lemma hypercube_succ (n : ℕ) : Q[n + 1] = Q[n].boxProd ⊤ := rfl

@[simp]
lemma hypercube_succ_adj {n : ℕ} {u v : HypercubeVert (n + 1)} :
    Q[n + 1].Adj u v ↔ (Q[n].Adj u.1 v.1 ∧ u.2 = v.2) ∨ (u.2 ≠ v.2 ∧ u.1 = v.1) :=
  Iff.rfl

/-!
Both `HypercubeVert` and `hypercube` are defined by recursion on `n`, so above we
recorded their defining equations as the lemmas `hypercubeVert_zero`,
`hypercubeVert_succ`, `hypercube_zero` and `hypercube_succ`, together with
`hypercube_succ_adj`, which spells out adjacency in `Q[n + 1]`. All five hold by
`rfl`, but only the two `_zero` lemmas and `hypercube_succ_adj` are marked as
`@[simp]`.

The `_zero` lemmas replace `HypercubeVert 0` and `Q[0]` by `Unit` and `⊥`, which
`simp` already knows a lot about, so they can only make a goal simpler. For example,
`simp` can prove `¬ Q[0].Adj u v` by chaining `hypercube_zero` with `bot_adj`.
-/
example (u v : HypercubeVert 0) : ¬ Q[0].Adj u v := by simp

/-!
The `_succ` lemmas just unfold the definition by one step, and we leave them out of
the `simp` set, as Mathlib does for recursive definitions (e.g. `pow_zero` is a
`simp` lemma but `pow_succ` is not). `simp` simplifies the parts of a term before the
term itself, so if `hypercube_succ` were a `simp` lemma it would turn `Q[n + 1]` into
`Q[n] □ ⊤` before any lemma about the hypercube got a chance to apply.

The exception is `hypercube_succ_adj`. It also unfolds a step, but only inside the
proposition `Q[n + 1].Adj u v`, which `simp` can rewrite wherever it occurs, and it
leaves the graph `Q[n + 1]` and its vertex type alone. Its right-hand side is what
Mathlib's `simp` lemmas `boxProd_adj` and `top_adj` would give if `simp` could see
that `Q[n + 1]` is a box product. With it, `simp` can check adjacency between
explicit vertices of `Q[n]` one coordinate at a time.

# Mycielskian

The *Mycielskian* of a graph `G : SimpleGraph V` is constructed as follows. Its
vertex set consists of two disjoint copies `Vₗ` and `Vᵣ` of `V` together with a new
apex vertex which we call `none`.

The edges inside `Vₗ` are identical to those of `G`; there are no edges inside `Vᵣ`;
there is an edge between vertices `a ∈ Vₗ` and `b ∈ Vᵣ` iff there is an edge in `G`
between the vertices of which `a` and `b` are copies. Finally `none` is adjacent to
every vertex in `Vᵣ` but to no vertices in `Vₗ`.

This construction is due to Jan Mycielski
[Mycielski 1955](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-mycielski-1955),
who showed that:

1. if `G` is triangle-free, then `mμ[G]` is also triangle-free.
2. if `G` has chromatic number `k`, then `mμ[G]` has chromatic number `k + 1`.

Thus starting with any triangle-free graph we can use it to construct triangle-free
graphs with arbitrarily large chromatic number.

In order to define the Mycielskian of a graph `G` in Lean we need to first describe
its vertex type. Given that it is built from two disjoint copies of the vertex type
of `G` together with a new vertex, we can use `Option (V ⊕ V)`. (We already saw the
`Sum` type `⊕` for `completeBipartiteGraph` and `Option` is the natural way to extend
a type with a new element called `none`.)
-/
section mycielskian_section
variable {V : Type*}

#source Option

/-- The *Mycielskian* of a graph `G`. -/
@[simps]
def mycielskian (G : SimpleGraph V) : SimpleGraph (Option (V ⊕ V)) where
  Adj x y := match x, y with
    | some (Sum.inl v), some (Sum.inl w) => G.Adj v w
    | some (Sum.inl v), some (Sum.inr w) => G.Adj v w
    | some (Sum.inr v), some (Sum.inl w) => G.Adj v w
    | none, some (Sum.inr w) => True
    | some (Sum.inr v), none => True
    | _, _ => False
  symm := ⟨by rintro (_ | _ | _) (_ | _ | _) h <;> simp_all [Adj.symm]⟩
  loopless := ⟨by rintro (_ | _ | _) <;> simp⟩

/-!
We introduce the notation `mμ[G]` for the Mycielskian of a graph `G`.
-/
@[inherit_doc mycielskian]
scoped notation "mμ[" G "]" => mycielskian G
/-!
As mentioned above if we iterate the Mycielskian construction starting with a
triangle-free graph then we obtain a sequence of triangle-free graphs with increasing
chromatic number.

In particular we can start with `K[2]`. Its Mycielskian is isomorphic to the
`5`-cycle `C[5]` (see [Vertex-Transitivity of
Mycielskians](#section-vertex-transitivity-of-mycielskians)), and the Mycielskian of
`C[5]` is called the *Grötzsch graph*
[Grötzsch 1959](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-grotzsch-1959).
-/
/-- The *Grötzsch graph* (i.e. the Mycielskian of `C[5]`). -/
@[simps!]
abbrev grotzschGraph : SimpleGraph (Option (Fin 5 ⊕ Fin 5)) := mμ[C[5]]

#check grotzschGraph_adj
/-!
[Figure: The Grötzsch graph (i.e. the Mycielskian of $C_5$)](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian.svg)

In order to talk about the vertices of `mμ[G]` it will be useful to introduce some
terminology. We name the two copies of `V` in a `mycielskian` namespace, since these
names only make sense for this construction. The `@[match_pattern]` attribute lets us
use them (and the notation below) as patterns when defining a function by pattern
matching, just like the constructors `none`, `some`, `Sum.inl` and `Sum.inr`.
-/
namespace mycielskian

/-- A copy of the vertex `v` in the "left" part of the Mycielskian. -/
@[match_pattern]
abbrev left (v : V) : Option (V ⊕ V) := some (Sum.inl v)

/-- A copy of the vertex `v` in the "right" part of the Mycielskian. -/
@[match_pattern]
abbrev right (v : V) : Option (V ⊕ V) := some (Sum.inr v)

end mycielskian

/-!
We can introduce notation for these as follows. The left copy of `v : V` is denoted
`v ₗ` and the right copy is denoted `v ᵣ`.
-/
@[inherit_doc mycielskian.left]
scoped postfix:max "ₗ" => mycielskian.left
@[inherit_doc mycielskian.right]
scoped postfix:max "ᵣ" => mycielskian.right

/-!
The `@[simps]` attribute on our definition of `mycielskian` generated a `@[simp]`
lemma `mycielskian_adj`, which rewrites `mμ[G].Adj x y` to the `match` in its
definition. Once both vertices are named, as in `v ₗ`, `w ᵣ` or `none`, `simp`
reduces the `match`, so it (and tactics such as `aesop` that call it) can decide any
adjacency between named vertices.
-/
example {G : SimpleGraph V} (v w : V) : mμ[G].Adj (v ₗ) (w ᵣ) ↔ G.Adj v w := by simp

example {G : SimpleGraph V} (v w : V) : ¬ mμ[G].Adj (v ᵣ) (w ᵣ) := by simp

/-!
We now prove a few lemmas about the Mycielskian construction that will be useful
later on.

The maps `v ↦ v ₗ` and `v ↦ v ᵣ` are injective. (In the proofs, `e |>.comp f` means
`(e).comp f`: the `|>.` lets us use dot notation on the result of
`Option.some_injective _` without extra brackets.)
-/
lemma mycielskian.left_injective : Function.Injective (fun v : V => v ₗ) :=
  Option.some_injective _ |>.comp Sum.inl_injective

lemma mycielskian.right_injective : Function.Injective (fun v : V => v ᵣ) :=
  Option.some_injective _ |>.comp Sum.inr_injective

/-!
The neighbourhoods of the vertices in `mμ[G]` are as follows.

A left copy `v ₗ` is adjacent to the left and right copies of the neighbours of `v`
in `G`.
-/
@[simp]
lemma neighborSet_mycielskian_left {G : SimpleGraph V} (v : V) :
    mμ[G].neighborSet (v ₗ) = (G.neighborSet v).image (· ₗ) ∪
      (G.neighborSet v).image (· ᵣ) := by
  ext x
  grind [mem_neighborSet, mycielskian_adj]

/-!
A right copy `v ᵣ` is adjacent to the left copies of the neighbours of `v` in `G`
and to `none`.
-/
@[simp]
lemma neighborSet_mycielskian_right {G : SimpleGraph V} (v : V) :
    mμ[G].neighborSet (v ᵣ) = insert none ((G.neighborSet v).image (· ₗ)) := by
  ext x
  grind [mem_neighborSet, mycielskian_adj]

/-!
The apex vertex `none` is adjacent to the right copies of all vertices in `G`.
-/
@[simp]
lemma neighborSet_mycielskian_none {G : SimpleGraph V} :
    mμ[G].neighborSet none = Set.range (· ᵣ) := by
  ext x
  grind [mem_neighborSet, mycielskian_adj]

/-!
The left copies, the right copies and `none` are pairwise disjoint.
-/
@[simp]
lemma mycielskian.disjoint_image_left_image_right (s t : Set V) :
    Disjoint (s.image (· ₗ)) (t.image (· ᵣ)) := by
  grind

@[simp]
lemma mycielskian.disjoint_image_left_none (s : Set V) :
    Disjoint (s.image (· ₗ)) {none} := by
  grind

@[simp]
lemma mycielskian.disjoint_image_right_none (s : Set V) :
    Disjoint (s.image (· ᵣ)) {none} := by
  grind

end mycielskian_section
/-!
As mentioned above we will be interested in iterating the Mycielskian construction,
but in order to do this we first need to define the iterated vertex type. (Below we
use `Type _` which means that the universe level is inferred (it will be the same as
the universe level of `V`). If you replaced `Type _` with `Type*`, the definition
would need to change.)

As with `HypercubeVert`, the `@[implicit_reducible]` attribute lets Lean unfold
`mμᵥ^(n + 1) V` when checking implicit and instance-implicit arguments.
-/

/-- The vertex type of the `n`-th Mycielskian of a `SimpleGraph V` (denoted
`mμᵥ^n V`). -/
@[implicit_reducible]
def MycielskianVert (V : Type*) : ℕ → Type _
  | 0     => V
  | n + 1 => Option (MycielskianVert V n ⊕ MycielskianVert V n)

@[simp]
lemma mycielskianVert_zero {V : Type*} : MycielskianVert V 0 = V := rfl

lemma mycielskianVert_succ {V : Type*} (n : ℕ) :
    MycielskianVert V (n + 1) =
      Option (MycielskianVert V n ⊕ MycielskianVert V n) := rfl

/-!
Notation for the vertex type of the `n`-th Mycielskian. Unlike `notation`, a `syntax`
declaration only tells Lean how to *parse* `mμᵥ^n V`. For Lean to also *print*
`MycielskianVert V n` as `mμᵥ^n V` (in goals, hovers and `#check` output) we add an
*unexpander*, which turns the application back into the notation.
-/
@[inherit_doc MycielskianVert]
scoped syntax "mμᵥ^" term:max ppSpace term:max : term
scoped macro_rules
  | `(mμᵥ^ $n $V) => `(MycielskianVert $V $n)

/-- Print `MycielskianVert V n` as `mμᵥ^n V`. -/
@[scoped app_unexpander MycielskianVert]
private def unexpandMycielskianVert : Lean.PrettyPrinter.Unexpander
  | `($_ $V $n) => `(mμᵥ^ $n $V)
  | _ => throw ()

/-- The `n`-th iterated Mycielskian of a graph `G` (denoted `mμ^n G`). -/
def iterMycielskian {V : Type*} (G : SimpleGraph V) : (n : ℕ) → SimpleGraph (mμᵥ^n V)
  | 0     => G
  | n + 1 => mμ[iterMycielskian G n]

@[simp]
lemma iterMycielskian_zero {V : Type*} (G : SimpleGraph V) :
    iterMycielskian G 0 = G := rfl

lemma iterMycielskian_succ {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    iterMycielskian G (n + 1) = mμ[iterMycielskian G n] := rfl

/-!
Notation for the iterated Mycielskian, again with an unexpander so that Lean prints
`iterMycielskian G n` as `mμ^n G`.
-/
@[inherit_doc iterMycielskian]
scoped syntax "mμ^" term:max ppSpace term:max : term
scoped macro_rules
  | `(mμ^ $n $G) => `(iterMycielskian $G $n)

/-- Print `iterMycielskian G n` as `mμ^n G`. -/
@[scoped app_unexpander iterMycielskian]
private def unexpandIterMycielskian : Lean.PrettyPrinter.Unexpander
  | `($_ $G $n) => `(mμ^ $n $G)
  | _ => throw ()

#check mμ^3 C[5]
/-!
The postfix operators `ₗ` and `ᵣ` can be stacked: `(0 : Fin 5)ₗᵣᵣ` means `((0ₗ)ᵣ)ᵣ`,
the right copy of the right copy of the left copy of `0`, which is a vertex of the
3rd iterated Mycielskian of `C[5]`. Written out in full this would be the unreadable
term `some (Sum.inr (some (Sum.inr (some (Sum.inl 0)))))`. The adjacency lemmas above
peel off one layer at a time: left–left and right–left pairs are adjacent exactly
when the underlying vertices are, so `(0 : Fin 5)ₗᵣᵣ` is adjacent to `(1 : Fin 5)ₗₗₗ`
because `0` and `1` are adjacent in `C[5]`. In the proof, `simpa [lemmas] using e`
simplifies both the goal and the type of `e`, then closes the goal with `e`.
-/
example : (mμ^3 C[5]).Adj (0 : Fin 5)ₗᵣᵣ (1 : Fin 5)ₗₗₗ := by
  simpa [iterMycielskian_succ] using (by decide : C[5].Adj 0 1)

/-!
# Complete Multipartite Graphs and Blow-ups *

Having earlier introduced complete bipartite graphs we would now like to discuss
complete multipartite graphs and their generalization: blow-up graphs. However these
constructions make use of the `SimpleGraph.comap` construction which we won't
formally introduce until [Comaps](#section-comaps). In order to properly understand
these constructions you may wish to read that short section now.

## Complete Multipartite Graphs
[Figure: A complete 4-partite graph](https://jt496.github.io/GraphTheoryInLean/figures/completemultipartite.svg)

A *complete multipartite* graph is a graph in which the vertices are partitioned into
classes so that two vertices are adjacent if and only if they are in different
classes. The definition in Mathlib looks rather forbidding at first glance:
-/
#source completeMultipartiteGraph  -- (V : ι → Type*) : SimpleGraph (Σ i, V i)
                                   --             := SimpleGraph.comap Sigma.fst ⊤

/-!
We start with an index type `ι` (the labels of the vertex classes) and a function
`V : ι → Type*`. The vertex type of the graph is `Σ i, V i`, the dependent pair or
`Sigma` type that we met in the definition of `SimpleGraph.sigma`.
-/
#source Sigma
/-!
Recall that a vertex `v : Σ i, V i` is a pair `⟨i, w⟩` consisting of an index
`i : ι` and an element `w : V i`; the class labelled by `i` is then the set of
vertices whose first component is `i`.

The `Sigma` type plays the same role here that the `Sum` type played in
`completeBipartiteGraph`. Just as a vertex of a sum type knows which of the two sides
it came from, since it is either a `Sum.inl` or a `Sum.inr`, a vertex of `Σ i, V i`
knows which class it lies in, since it carries its index. The two alternatives
`Sum.inl` and `Sum.inr` have simply been replaced by one alternative for each
`i : ι`.
-/
#check Sigma.fst -- The first component of a dependent pair `⟨i, w⟩`.
/-!
The `SimpleGraph.comap` then defines edges in the graph by pulling back the adjacency
relation from `⊤ : SimpleGraph ι`, the complete graph on `ι`, using `Sigma.fst`. So
vertices are adjacent if and only if their first components are different.
-/
#source SimpleGraph.comap
/-!
Adjacency in this graph is then exactly as we would expect: two vertices `⟨i, u⟩` and
`⟨j, v⟩` are adjacent iff they belong to different classes, i.e. `i ≠ j`.
-/
lemma completeMultipartiteGraph_adj {ι : Type*} (V : ι → Type*) (u v : Σ i, V i) :
    (completeMultipartiteGraph V).Adj u v ↔ u.fst ≠ v.fst := Iff.rfl

/-!
As an example, the complete multipartite graph with `n` classes, where each class is
a copy of `ℕ` can be defined as follows.
-/
/-- The complete multipartite graph with `n` classes, where each class is a copy of
`ℕ`. -/
@[simps!]
abbrev multiNat (n : ℕ) : SimpleGraph (Σ _ : Fin n, ℕ) :=
  completeMultipartiteGraph fun (_ : Fin n) => ℕ

#check multiNat_adj -- produced by the `@[simps!]` attribute on `multiNat`

/-!
We can also define the complete multipartite graph with classes indexed by `ℕ`, where
the `n`-th class is `Fin n`.
-/
/-- The complete multipartite graph with classes indexed by `ℕ`, where the `n`-th
class is `Fin n`. -/
@[simps!]
abbrev natFinMulti : SimpleGraph (Σ n : ℕ, Fin n) :=
  completeMultipartiteGraph (fun n => Fin n)

#check natFinMulti_adj

/-!
Deciding whether two vertices are adjacent in a complete multipartite graph is easy:
they are adjacent if and only if their first components are different. So
decidability of adjacency follows from decidability of equality on their index type.
Since `Fin n` and `ℕ` have decidable equality, `multiNat` and `natFinMulti` have
decidable adjacency.
-/
example : (multiNat 3).Adj ⟨0, 12⟩ ⟨2, 10⟩ := by decide

example : ¬ natFinMulti.Adj ⟨3, 0⟩ ⟨3, 1⟩ := by decide

/-!
## Blow-ups

While not currently in Mathlib we can define the *blow-up* of a graph `G`.
Informally, this is the graph obtained from `G` by replacing each vertex with a class
of vertices and defining edges between vertices in different classes according to the
edges in `G`. (This is a trivial generalization of the `completeMultipartiteGraph`
construction, which is the special case where `G` is a complete graph.)
-/
/-- The blow-up of a graph `G` given by replacing each vertex `i` with a class of
vertices `V i`. -/
@[simps!]
abbrev blowUpGraph {ι : Type*} (G : SimpleGraph ι) (V : ι → Type*) :
    SimpleGraph (Σ i, V i) := SimpleGraph.comap Sigma.fst G

#check blowUpGraph_adj -- (G.blowUpGraph V).Adj u v = G.Adj u.fst v.fst

/-!
The `n`-uniform blow-up of a graph `G` is the blow-up of `G` where each vertex is
replaced by a class of size `n`.
-/
/-- The `n`-uniform blow-up of a graph `G` given by replacing each vertex `i` with
`n` vertices (`Fin n`), denoted `G[n]`. -/
@[simps!]
abbrev blowUpN {ι : Type*} (G : SimpleGraph ι) (n : ℕ) :
    SimpleGraph (Σ _ : ι, Fin n) := G.blowUpGraph (fun _ => Fin n)

/-!
We introduce the notation `G[n]` for the `n`-uniform blow-up of `G`.
-/
@[inherit_doc blowUpN]
scoped notation:max G "[" n "]" => blowUpN G n

#check C[4][3] -- the blow-up of `C[4]` replacing each vertex by a class of size `3`
example : C[4][3].Adj ⟨1, 0⟩ ⟨2, 0⟩ := by decide
example : ¬ C[4][3].Adj ⟨0, 0⟩ ⟨2, 1⟩ := by decide

/-!
[Figure: The 3-uniform blow-up of $C_4$](https://jt496.github.io/GraphTheoryInLean/figures/blowup_c4.svg)

# Kneser Graphs *

The `k`-th Kneser graph
[Kneser 1955](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-kneser-1955)
on a type `β` has as vertices the `k`-element subsets of `β`, with edges between any
distinct disjoint subsets. Before we can define this as a `SimpleGraph` we need to
decide what the vertex type should be. If we are happy to work with finite types
(i.e. to assume `Fintype β`) then we could use
`(Finset.univ : Finset β).powersetCard k` which is the finite family of `k`-element
subsets of a finite type `β`.
-/
#check Finset.powersetCard
/-!
Using `Finset.powersetCard` gives us easy access to lots of counting results about
families of finite sets, which would be useful.

But there are two drawbacks. Firstly, the finiteness assumption is a bit restrictive.
Secondly, this vertex type mentions `Finset.univ`, and hence the `Fintype β`
instance: two different instances give vertex types that are equal but not
definitionally equal, so a lemma proved for one does not apply to the other. (Since
we won't use this definition we mark it `private`.)
-/
@[simps]
private def kneserGraphFintype (β : Type*) [Fintype β] (k : ℕ) :
    SimpleGraph ((Finset.univ : Finset β).powersetCard k) where
  Adj u v := Disjoint u.val v.val ∧ u ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-!
Instead we use the subtype of `Finset β` consisting of `k`-element subsets, i.e.
`{s : Finset β // s.card = k}`. This means we no longer need to assume `Fintype β`
but we lose direct access to the `Finset.powersetCard` results. However we can solve
this issue with a simple translation lemma saying that, for any predicate `p`,
counting the `k`-element subsets satisfying `p` as terms of the subtype
`{s : Finset β // s.card = k}` gives the same answer as counting them as members of
the family `(Finset.univ : Finset β).powersetCard k`. (See [Independence Number of
the Kneser Graph*](#section-independence-number-of-the-kneser-graph) for details.)
-/
/-- The `k`-th Kneser graph on `β`: vertices are `k`-element subsets of `β`, and
edges join disjoint, distinct subsets. -/
@[simps]
def kneserGraph (β : Type*) (k : ℕ) :
    SimpleGraph {s : Finset β // s.card = k} where
  Adj u v := Disjoint u.val v.val ∧ u ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

#check kneserGraph_adj -- (kneserGraph β k).Adj u v = (Disjoint ↑u ↑v ∧ u ≠ v)

instance (β : Type*) (k : ℕ) [DecidableEq β] :
    DecidableRel ((kneserGraph β k).Adj) := fun u v => by
  unfold kneserGraph; infer_instance

/-!
We introduce the notation `Kn[n, k]` for the `k`-th Kneser graph on `Fin n`.
-/
/-- The `k`-th Kneser graph on `Fin n`: vertices are `k`-element subsets of `Fin n`,
and edges join disjoint, distinct subsets. -/
scoped notation "Kn[" n ", " k "]" => kneserGraph (Fin n) k

/-!
A special case of the Kneser graph is the *Petersen* graph
[Petersen 1898](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-petersen-1898),
which is `Kn[5, 2]`.
-/
/-- The *Petersen* graph which is the Kneser graph `Kn[5, 2]`. -/
abbrev petersenGraph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} := Kn[5, 2]

/-!
[Figure: The Petersen graph as the Kneser graph $Kn(5,2)$](https://jt496.github.io/GraphTheoryInLean/figures/petersen.svg)

We will look at the independence number of `Kn[n, k]` in [Cliques](#chapter-cliques)
and colourings of `Kn[n, k]` in [Exercises](#section-exercises-colorings). Computing
its independence number is really just a case of translating the Erdős–Ko–Rado
theorem (which is in Mathlib) into the language of `SimpleGraph`.
-/
end SimpleGraph
