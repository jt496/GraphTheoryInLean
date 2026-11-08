/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.Common
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace SimpleGraph
/-!
In this chapter we introduce the basics of `SimpleGraph`, Mathlib's definition of a
simple, loopless, undirected graph. We will explore how adjacency, edges, darts, and
neighbourhoods are defined. We will also look at the process of constructing a graph
(the infinite path on `ℕ`) using a few different methods. Finally we will look at how
to perform basic computations on graphs.

# SimpleGraph

Mathlib already contains a few different definitions of graphs (for example directed
graphs as `Digraph` and multigraphs as `Graph`), but we will only look at
`SimpleGraph`. (Although `SimpleGraph` is currently the most commonly used
graph structure in Mathlib, it has some real limitations: for example any
non-spanning subgraph of a `SimpleGraph V` is *not* a `SimpleGraph V`. However, it
has a well-developed API and many results can be formalized with relative ease.)

The definition of `SimpleGraph` in Mathlib says that, for a fixed vertex type `V`, a
term of `SimpleGraph V` is a structure consisting of a binary relation `Adj` on `V`
that tells us which pairs of vertices are adjacent, and two proofs `symm` and
`loopless` that this relation is symmetric and irreflexive. (We can omit proofs
of `symm` and `loopless` and Lean will try to fill them in using the automated
`aesop_graph` tactic.) Note that `V` is a parameter of the structure rather
than one of its fields: graphs on different vertex types have different types.
-/
section basics
variable {V : Type*} (G : SimpleGraph V)

#source SimpleGraph -- structure SimpleGraph (V : Type u) where
                    --  Adj : V → V → Prop
                    --  symm : Std.Symm Adj := by aesop_graph
                    --  loopless : Std.Irrefl Adj := by aesop_graph

#check G.Adj        -- a relation on V describing adjacency in `G`
#check G.symm       -- adjacency is symmetric (undirected edges)
#check G.loopless   -- adjacency is irreflexive (no loops)
/-!
Both `Std.Symm Adj` and `Std.Irrefl Adj` are structures with a single field, namely
`symm : ∀ a b, Adj a b → Adj b a` and `irrefl : ∀ a, ¬Adj a a`. So to give these
proofs by hand we write `symm := ⟨fun a b h => …⟩` (or give a tactic proof with
`symm := by constructor; …`).

We will meet the formal definition of a graph's edges in a moment, but usually we
reason directly with the adjacency relation `G.Adj`. Informally we write `u — v` for
an edge of `G` joining `u` and `v`; in Lean we instead work with a proof `h` of the
proposition `G.Adj u v : Prop`. (Strictly speaking, `h : G.Adj u v` records the
*directed* edge `u → v`, but by symmetry it also gives `G.Adj v u`, namely `h.symm`,
so we can treat it as the undirected edge `u — v`.)
-/
example {u v : V} (h : G.Adj u v) : G.Adj v u := h.symm
/-!
The fact that `G` does not have a loop at a vertex `u` is the proposition
`¬ G.Adj u u`.
-/
example {u : V} : ¬ G.Adj u u := G.irrefl
/-!
# Edges

Since `SimpleGraph` is a loopless undirected graph, its edges are *unordered* pairs
of distinct vertices. In Lean unordered pairs have type `Sym2 V`, the symmetric
square of `V`. Formally this is the quotient of `V × V` modulo swaps (`Sym2.Rel`).
Elements (or more precisely terms) of `Sym2 V` are denoted `s(u, v)`. Note that
although `s(v, v)` cannot be an edge of a `SimpleGraph` (which is loopless), the
type `Sym2 V` still contains such pairs.
-/
example {u v : V} : s(u, v) = s(v, u) := Sym2.eq_swap
/-!
The *edge set* of `G` is `G.edgeSet` and is a `Set (Sym2 V)`. Membership is
definitionally equivalent to adjacency. (This means that the proof is `rfl`.)
-/
example {u v : V} : s(u, v) ∈ G.edgeSet ↔ G.Adj u v := by rfl
/-!
However using `G.Adj u v` has a couple of advantages over `s(u, v) ∈ G.edgeSet`: it
avoids the need for `Sym2 V` and, via dot notation, we have easy access to convenient
lemmas about adjacency.
-/
#check Adj.ne -- G.Adj a b → a ≠ b
example {u v : V} (h : G.Adj u v) : u ≠ v := h.ne
example {u v : V} (h : G.Adj u v) : v ≠ u := h.ne'
/-!
Generally we prefer to use `G.Adj u v` rather than `s(u, v) ∈ G.edgeSet` when talking
about individual edges, but when we want to talk about a *set* of (possible) edges of
a graph then `s : Set (Sym2 V)` is what we need.

When we do need to prove something about an arbitrary `e : Sym2 V`, the usual first
step is `induction e using Sym2.ind`. Every term of `Sym2 V` is `s(x, y)` for some
`x y : V`, and `Sym2.ind` reduces the goal to that case. For example, no edge of `G`
is a loop. Mathlib calls a pair of the form `s(v, v)` *diagonal* (`Sym2.IsDiag`).
-/
example (e : Sym2 V) (he : e ∈ G.edgeSet) : ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ x y =>                 -- he : s(x, y) ∈ G.edgeSet ⊢ ¬s(x, y).IsDiag
    rw [mem_edgeSet] at he
    rw [Sym2.mk_isDiag_iff]
    exact he.ne

/-!
Notice that `induction` replaced `e` by `s(x, y)` in the hypothesis `he` as well as
in the goal. This result is `G.not_isDiag_of_mem_edgeSet` in Mathlib.

# Vertices

The vertex set of a `SimpleGraph V` is `V` (although strictly speaking `V` is a type,
not a set). These can be infinite (`ℕ`), or empty (`Fin 0`). Nonemptiness and
finiteness are extra hypotheses that need to be stated: for example as `[Nonempty V]`
and `[Fintype V]`. See [Decidability, Finiteness and
Degrees](#chapter-decidability-finiteness-and-degrees) for more details.

Mathlib defines a number of useful subsets of `V` (terms `s : Set V`), in
particular the `support` of the graph and the `neighborSet` of a vertex. (We can
refer to the entire vertex set of a `SimpleGraph V` as a *set* by
`Set.univ : Set V`.)

## Support

The *support* of a graph is the set of vertices that belong to at least one edge.
-/
#check mem_support -- (G : SimpleGraph V) {v : V} : v ∈ G.support ↔ ∃ w, G.Adj v w

/-!
If `G.Adj u v` then `u` is in the support of `G`.
-/
example {u v : V} (h : G.Adj u v) : u ∈ G.support := h.left_mem_support
/-!
Notice that in the previous example we could use `h.left_mem_support` where
`h : G.Adj u v` since the theorem we applied is in the `SimpleGraph.Adj` namespace.
Also note the use of "left" in the name of the lemma. You should be able to guess
how to prove `v ∈ G.support` from `h : G.Adj u v`.
-/
#check SimpleGraph.Adj.left_mem_support

/-!
## Neighbours

The *neighbours* of a vertex `v` in a graph `G` are the vertices adjacent to `v`.
-/
#source neighborSet -- def neighborSet (v : V) : Set V := {w | G.Adj v w}

example {u v : V} : G.Adj u v ↔ v ∈ G.neighborSet u := by rfl

example {u : V} : G.neighborSet u ⊆ G.support := by
  intro v hv
  exact ⟨u, hv.symm⟩

/-!
This result is also in Mathlib.
-/
example {u : V} : G.neighborSet u ⊆ G.support := G.neighborSet_subset_support u

/-!
The *incidence set* of `v` is the set of edges that contain `v`. (For `e : Sym2 V`,
`v ∈ e` means that `v` is one of the two endpoints of `e`.) A vertex is *isolated* if
it has no neighbours; it is *universal* if it is adjacent to every other vertex.
-/
#source incidenceSet -- {e ∈ G.edgeSet | v ∈ e}
#check mem_incidenceSet -- s(v, w) ∈ G.incidenceSet v ↔ G.Adj v w
#source IsIsolated -- ∀ w, ¬G.Adj v w
#source IsUniversal -- ∀ ⦃w⦄, v ≠ w → G.Adj v w

/-!
The braces `∀ ⦃w⦄` in the definition of `IsUniversal` mark `w` as a *strict-implicit*
argument: Lean fills it in like `{w}`, but only once a later explicit argument (here
the proof of `v ≠ w`) is supplied.

### Sets as Types

Although `G.neighborSet u` is a `Set V`, Lean also lets us use it as a *type*. A term
`w : G.neighborSet u` is a vertex together with a proof that this vertex is a
neighbour of `u`.

Lean displays this type as `↑(G.neighborSet u)`: it is the *subtype*
`{w : V // w ∈ G.neighborSet u}`. We build such terms with the anonymous constructor
`⟨v, h⟩` and take them apart with `.val` (the vertex) and `.property` (the proof).
Lean inserts `.val` automatically wherever a term of `V` is expected, and displays it
as `↑w`.
-/
example {u v : V} (h : G.Adj u v) : G.neighborSet u := ⟨v, h⟩

example {u : V} (w : G.neighborSet u) : G.Adj u w.val := by
  exact w.property

example {u : V} (w : G.neighborSet u) : G.Adj u w := by
  exact w.property

/-!
# Darts

Since edges in `SimpleGraph` are undirected it might seem strange to introduce the
notion of a dart (an oriented edge). However we already noted that `h : G.Adj u v`
has a direction to it; darts simply give us a way to talk about the ordered pairs of
adjacent vertices in a graph. These can be very useful, for example in double
counting arguments such as proving the *handshake lemma*.

A *dart* `d : G.Dart` is an ordered pair of vertices together with a proof that they
are adjacent in `G`. Since edges are unoriented, darts come in symmetric pairs: if
`d : G.Dart` then `d.symm` is the opposite dart and `d.edge` is the edge
corresponding to `d`.
-/
section darts
#source Dart

variable (d : G.Dart)
#check d.fst  -- the first vertex of the dart
#check d.snd  -- the second vertex of the dart
#check d.adj  -- the adjacency proof of the dart
#check d.edge -- the edge corresponding to the dart
#check d.symm -- the opposite dart from `d.snd` to `d.fst`

/-!
Edges are unoriented so `d` and `d.symm` correspond to the same edge.
-/
example : d.symm.edge = d.edge :=
  Dart.edge_symm d

example : d.fst = d.symm.snd := rfl

end darts

/-!
# Naming Conventions

We have now met a few Mathlib names, and they follow fixed patterns. Knowing the
rules will help us guess a lemma's name. The full rules can be found in Mathlib's
[naming conventions](https://leanprover-community.github.io/contribute/naming.html).
The key points are:

* Theorems are named in `snake_case`, predicates and structures in `UpperCamelCase`
  (`IsIsolated`, `Dart`) and other definitions in `lowerCamelCase` (`neighborSet`).
* A theorem's name describes its statement, with the conclusion first and any
  hypotheses after `of`. Symbols have standard names: `¬` is `not`, `∈` is `mem`,
  `⊆` is `subset`, `≠` is `ne`, `∉` is `notMem` and `⊤` is `top`. So
  `not_isDiag_of_mem_edgeSet` says that an edge `e ∈ G.edgeSet` is not a loop, and
  `neighborSet_subset_support` says that `G.neighborSet u ⊆ G.support`.
* An equivalence (`↔`) that characterises membership of a set, such as `mem_edgeSet`
  or `mem_support`, is named after its left-hand side alone. Other equivalences often
  end in `_iff`, such as `Sym2.mk_isDiag_iff`.
* A theorem about `h : G.Adj u v` lives in the namespace `SimpleGraph.Adj`, so we can
  use it with dot notation, as with `h.ne` and `h.left_mem_support`. A prime marks a
  minor variant, so `h.ne` proves `u ≠ v` while `h.ne'` proves `v ≠ u`.

When the rules don't allow us to guess the name, we can search for it as described in
[Finding Lemmas](#section-finding-lemmas).

# Order

There is a partial order on `SimpleGraph V` given by `G ≤ H` iff `G` is a subgraph of
`H`. (Note that these are necessarily spanning subgraphs since all
`SimpleGraph V` have the same vertex set. We will consider general subgraphs later,
see [Subgraphs](#chapter-subgraphs).)

This gives `SimpleGraph V` the structure of a *complete atomic Boolean algebra*, with
operations `sup` (`⊔`), `inf` (`⊓`), `compl` (`ᶜ`) and `sdiff` (`\`), and elements
`top` (`⊤`) and `bot` (`⊥`). This terminology comes from order theory rather than
graph theory, but it is very natural in the context of formalization. Here *complete*
means that every set of graphs in `SimpleGraph V` has a supremum (the graph whose
edges are those present in at least one graph in the set) and an infimum (the graph
whose edges are those present in every graph in the set). The *atoms* of
`SimpleGraph V` are the graphs with exactly one edge, and *atomic* means that every
graph is the supremum of the atoms below it, i.e. the union of its single-edge
subgraphs. Mathlib registers this structure as an *instance*, which Lean supplies
automatically wherever it is needed. The command `#synth` asks Lean to find
(synthesize) an instance and shows it; we will say more about instances in
[Decidability, Finiteness and Degrees](#chapter-decidability-finiteness-and-degrees).
-/
section order

#synth CompleteAtomicBooleanAlgebra (SimpleGraph V)

#source SimpleGraph.instLE -- le x y := ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

variable (H : SimpleGraph V)
#check G ≤ H

/-!
The definition of *proper* subgraph (`G < H`) is phrased differently to how we might
expect. Rather than `G < H ↔ G ≤ H ∧ G ≠ H` we have:
-/
example : G < H ↔ G ≤ H ∧ ¬ H ≤ G := by rfl
/-!
Of course they are equivalent.
-/
example : G < H ↔ G ≤ H ∧ G ≠ H := lt_iff_le_and_ne
/-!
The *sup* of `G` and `H`, denoted `G ⊔ H`, is the `SimpleGraph V` in which any pair
of vertices from `V` are adjacent iff they are adjacent in `G` or `H` (i.e. it is the
union of `G` and `H`).
-/
#check sup_adj

/-!
The *inf* of `G` and `H`, denoted `G ⊓ H`, is the `SimpleGraph V` in which any pair
of vertices from `V` are adjacent iff they are adjacent in both `G` and `H` (i.e. it
is the intersection of `G` and `H`).

[Figure: Top: graphs $G$ (blue) and $H$ (red) on the same vertices. Bottom: their inf $G \sqcap H$ (left) and sup $G \sqcup H$ (right), with the edges in both graphs in green](https://jt496.github.io/GraphTheoryInLean/figures/inf.svg)
-/
#check inf_adj

/-!
The *complement* of `G`, denoted `Gᶜ`, is the `SimpleGraph V` in which the edges are
all pairs of distinct vertices that are not adjacent in `G`.
-/
#check compl_adj

/-!
The *set difference* of two graphs, denoted `G \ H`, has the edges of `G` with the
edges of `H` removed. (Since the resulting graph is a `SimpleGraph V` the vertices
are necessarily unchanged.)
-/
#check sdiff_adj

/-!
[Figure: Top: graphs $G$ and $H$. Bottom: the complement $G^c$ (left) and the set difference $G \setminus H$ (right)](https://jt496.github.io/GraphTheoryInLean/figures/sdiff.svg)

We can remove a set of edges `s : Set (Sym2 V)` from a graph `G` to form
`G.deleteEdges s`. If `s = H.edgeSet` then this is the same as the set difference
`G \ H`.
-/
#source deleteEdges
#check deleteEdges_adj      -- (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s
#check deleteEdges_edgeSet  -- G.deleteEdges H.edgeSet = G \ H

/-!
## Top and Bottom

The *complete graph* `⊤` has all possible edges (every pair of distinct vertices is
adjacent), while the *empty graph* `⊥` has no edges. These are the greatest and least
elements of the subgraph order. Although `completeGraph V` and `emptyGraph V` are
abbreviations for `⊤` and `⊥`, we generally use `top` and `bot` in naming results
about these graphs.
-/

#check top_adj  -- (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w
#check bot_adj  -- (⊥ : SimpleGraph V).Adj v w ↔ False

/-!
Every graph is a subgraph of the complete graph.
-/
example : G ≤ ⊤ := le_top

/-!
The empty graph is a subgraph of every graph.
-/
example : ⊥ ≤ G := bot_le

/-!
If `G` is a proper subgraph of `H` then `G` is a proper subgraph of the complete
graph.
-/
example {G H : SimpleGraph V} (h : G < H) : G < ⊤ := lt_top_of_lt h

end order
end basics
/-!
Notice that the last few proofs all made use of results about orders rather than
anything specific to graphs. They all follow easily from Mathlib's instance of
`CompleteAtomicBooleanAlgebra (SimpleGraph V)`, which we displayed with `#synth` at
the start of this section.
-/
/-!
# Constructing a SimpleGraph

The simplest way to build a `SimpleGraph` is with its default constructor:
`SimpleGraph.mk`, supplying an adjacency relation together with proofs of symmetry
and irreflexivity. In many cases (such as below) the tactic `aesop_graph` can
discharge one or both proofs so they can be omitted. In this section we will look at
three different ways of constructing the same graph: the path graph on `ℕ`.
-/

/-- The path graph on `ℕ` defined using the default constructor, with `x` and `y`
adjacent iff `x + 1 = y` or `y + 1 = x`. -/
@[simps]
abbrev pathNat : SimpleGraph ℕ where
  Adj x y := x + 1 = y ∨ y + 1 = x

/-!
The `@[simps]` attribute automatically generates the `simp` lemma `pathNat_adj`. An
*attribute*, written `@[…]` before a declaration, tells Lean to do something extra
with the declaration once it is defined: `@[simp]` registers a lemma for use by
`simp`, and `@[simps]` generates `simp` lemmas from a definition. (If you want to see
which lemmas are generated by a `@[simps]` attribute you can change it to `@[simps?]`
and the InfoView will tell you.)
-/
#check pathNat_adj -- pathNat.Adj x y = (x + 1 = y ∨ y + 1 = x)

/-!
Another way to construct the same graph is to use the `SimpleGraph.fromRel`
constructor which symmetrizes any given relation and removes loops. (The
expression `(· + 1 = ·)` below is shorthand for the relation
`fun x y => x + 1 = y`.)
-/
#source SimpleGraph.fromRel

/-- The path graph on `ℕ` defined using `SimpleGraph.fromRel`. -/
@[simps!]
def pathNatFromRel : SimpleGraph ℕ := SimpleGraph.fromRel (· + 1 = ·)

/-!
This time we used `@[simps!]` rather than `@[simps]`. Plain `@[simps]` reads its
lemmas straight off a definition written as a structure, as `pathNat` was (using
`where`), since the value of each field is written out explicitly. The body of
`pathNatFromRel` is instead an application of `fromRel`, so to find `Adj` it must
first unfold `fromRel` and then tidy up the result with `simp`. The `!` asks for
both. (If we wrote `@[simps]` here, a linter warning would suggest `@[simps!]`.)
-/
#check pathNatFromRel_adj -- pathNatFromRel.Adj a b =
                          --   (¬a = b ∧ (a + 1 = b ∨ b + 1 = a))

/-!
Also notice that `pathNatFromRel` is a `def`, whereas `pathNat` (and
`pathNatFromEdgeSet` below) are `abbrev`s. The difference is that an `abbrev` is a
definition that Lean unfolds automatically when it needs to. This is deliberate: we
will see in [Decidability, Finiteness and
Degrees](#chapter-decidability-finiteness-and-degrees) how this choice affects Lean's
ability to compute with these graphs.

The two graphs `pathNat` and `pathNatFromRel` are equal, but not *definitionally*
equal: `rfl` does not prove the equality. We explain this important distinction in
[Definitional and Propositional
Equalities](#section-definitional-and-propositional-equalities) below.

In order to prove this we need to show that they have the same adjacency relation
(i.e. the same edges). We *don't* need to check that they have the same vertex sets
since this is done automatically by the type system: both `pathNat` and
`pathNatFromRel` are `SimpleGraph ℕ`.

Lean's type checker ensures that we can't even state a theorem saying that two graphs
with different vertex sets are equal. For example if `G : SimpleGraph V` then the
expression `G = pathNat` is not well-typed since `pathNat` has vertex type `ℕ` and
`G` has vertex type `V`.
-/
/-- error: Type mismatch
  pathNat
has type
  SimpleGraph.{0} ℕ -/
#guard_msgs (substring := true) in
example {V : Type*} (G : SimpleGraph V) : G = pathNat := by
  sorry

/-!
Any two graphs on the same vertex type with the same edges are equal by
*extensionality*, and we can use the `ext` tactic to prove that `pathNat` and
`pathNatFromRel` are equal. The definition of `SimpleGraph` is tagged with the
`@[ext]` attribute which gives us the following `ext` lemmas for free.
-/
#check SimpleGraph.ext
#check SimpleGraph.ext_iff
/-!
The `ext` tactic reduces the goal to showing that for all `a` and `b`,
`pathNat.Adj a b ↔ pathNatFromRel.Adj a b`. After rewriting with the two adjacency
lemmas, what remains is a statement of logic and arithmetic about natural numbers,
which `grind` proves. `grind` is an automated tactic that combines case splitting,
congruence closure and linear arithmetic; we use it throughout this guide to finish
off goals of this kind, and say more about it in [Grind](#section-grind).
-/

example : pathNat = pathNatFromRel := by
  ext a b
  -- now rewrite using the definition of adjacency in both graphs
  rw [pathNat_adj, pathNatFromRel_adj]
  -- the goal is now to show that the two relations are equivalent
  -- ⊢ a + 1 = b ∨ b + 1 = a ↔ ¬a = b ∧ (a + 1 = b ∨ b + 1 = a)
  grind

/-!
A third way to construct a `SimpleGraph` is from a set of edges `s : Set (Sym2 V)`.
(Recall that edges are unordered pairs of vertices, which have type `Sym2 V` in
Lean.)
-/
#source SimpleGraph.fromEdgeSet

/-- The path graph on `ℕ` defined using `SimpleGraph.fromEdgeSet`. -/
@[simps!]
abbrev pathNatFromEdgeSet : SimpleGraph ℕ :=
  SimpleGraph.fromEdgeSet {e | ∃ n, e = s(n, n + 1)}

/-!
Again we can show that `pathNatFromEdgeSet` is equal to `pathNat` using `ext` (hence
all three definitions agree).
-/
lemma pathNat_eq_pathNatFromEdgeSet : pathNat = pathNatFromEdgeSet := by
  ext a b
  rw [pathNat_adj, pathNatFromEdgeSet_adj]
  grind

/-!
We can also state this equality in terms of adjacency, which is usually more
convenient.
-/
lemma pathNat_adj_iff_pathNatFromEdgeSet {x y : ℕ} :
    pathNat.Adj x y ↔ pathNatFromEdgeSet.Adj x y := by
  rw [pathNat_eq_pathNatFromEdgeSet]

/-!
## Definitional and Propositional Equalities

All three of our path graphs are equal, but Lean distinguishes two kinds of equality.
An equality `a = b` is *definitional* if both sides *unfold* to the same term, so
that `rfl` proves it; we then say that `a` and `b` are *definitionally equal*, or
*defeq* for short. Otherwise the equality is merely *propositional*: it may still be
true, but it needs a genuine proof. (Every definitional equality is also
propositional, with proof `rfl`.) The equality `pathNat = pathNatFromRel` is
propositional but not definitional: we proved it with `ext` and a short argument
about natural numbers, while `rfl` fails.
-/
/-- error: Tactic `rfl` failed: The left-hand side
  pathNat
is not definitionally equal to the right-hand side
  pathNatFromRel -/
#guard_msgs (substring := true) in
example : pathNat = pathNatFromRel := by rfl

/-!
Here *unfolding* means more than replacing names by their definitions: Lean also
*computes* (or *reduces*), running any recursion or pattern match whose argument it
can see is a constructor. For example `+` on `ℕ` is defined by recursion on its
second argument, so `n + 0` reduces to `n` even for a variable `n`, and `rfl` proves
`n + 0 = n`. But in `0 + n` the recursion is on the variable `n`, which is neither
`0` nor a successor, so the computation is *stuck*: `0 + n = n` is true, but only
propositionally, and its proof needs induction on `n`.
-/
example (n : ℕ) : n + 0 = n := by rfl

/-- error: Tactic `rfl` failed: The left-hand side
  0 + n
is not definitionally equal to the right-hand side
  n -/
#guard_msgs (substring := true) in
example (n : ℕ) : 0 + n = n := by rfl

/-!
The distinction matters more in Lean than on paper. Lean's type checker, and its
matching of terms when we apply a lemma, only see definitional equalities, so two
things that are merely propositionally equal cannot be used interchangeably without
an explicit step.

Definitionally equal statements, on the other hand, are interchangeable, and the
`change` tactic lets us restate one as another: `change t` replaces the goal by `t`,
provided the two are definitionally equal (and `change t at h` does the same for a
hypothesis `h`). One use is to unfold a definition that automation cannot see
through. Below, `grind` fails on the goal `pathNatFromRel.Adj x (x + 1)`, but once
`change` has unfolded `pathNatFromRel` and `fromRel` the goal is about natural
numbers, and `grind` proves it. By contrast, `change pathNat.Adj x (x + 1)` would
fail, since `pathNat` and `pathNatFromRel` are not definitionally equal.
-/
example (x : ℕ) : pathNatFromRel.Adj x (x + 1) := by
  change x ≠ x + 1 ∧ (x + 1 = x + 1 ∨ x + 1 + 1 = x)
  grind

/-!
Relying on how a definition happens to unfold is sometimes called *defeq abuse*.
The proof above depends on the implementation of Mathlib's `fromRel` and might break
if that changed, whereas `rw [pathNatFromRel_adj]` (or just `simp`) relies only on a
stated lemma. So when a definition comes with lemmas describing it, prefer them, and
keep `change` for goals where no such lemma is available.

## The Simplifier

The `simp` tactic, Lean's *simplifier*, will be one of our most frequently used
tactics, so it is worth knowing how it works. It rewrites the goal using the lemmas
in the *`simp` set*, which consists of all the lemmas tagged `@[simp]` (including
those generated by `@[simps]`) in Mathlib and in the files we import. Each of these
lemmas is an equation or an `↔`, which `simp` uses to rewrite from *left* to *right*.
It simplifies the parts of a term before the term itself, and keeps going until no
lemma applies. If the goal has become `True` (for example an equation whose two sides
are the same) then `simp` closes it. The most common variants are:

* `simp at h` simplifies the hypothesis `h` instead of the goal;
* `simp [foo, h]` also rewrites with the lemma `foo` and the hypothesis `h`, while
  `simp [-foo]` stops it from using the `simp` lemma `foo`;
* `simp_all` simplifies the goal and all the hypotheses, using each hypothesis to
  simplify the others and the goal, and is applied until nothing changes;
* `simp only [foo, h]` rewrites with just the listed lemmas and hypotheses.

`simp?` works exactly like `simp`, but also suggests a `simp only` call listing the
lemmas that were actually used (clicking on the suggestion in the InfoView replaces
`simp?` by it). Running it on the adjacency relations of our three path graphs gives
three different answers.
-/
example (a b : ℕ) : pathNatFromRel.Adj a b ↔ a ≠ b ∧ (a + 1 = b ∨ b + 1 = a) := by
  simp? -- Try this: simp only [pathNatFromRel_adj, ne_eq]

example (a b : ℕ) : pathNat.Adj a b ↔ a + 1 = b ∨ b + 1 = a := by
  simp? -- Try this: simp only

example (a b : ℕ) : pathNatFromEdgeSet.Adj a b ↔
    (∃ n, a = n ∧ b = n + 1 ∨ a = n + 1 ∧ b = n) ∧ a ≠ b := by
  simp? -- Try this: simp only [fromEdgeSet_adj, Set.mem_ofPred_eq, Sym2.eq, ...]

/-!
Two things determine what `simp` does here: whether it can see inside the definition,
and what it finds there. `simp` does not unfold a `def` (unless we ask it to, with
`simp [pathNatFromRel]`), so all it can do with `pathNatFromRel.Adj a b` is rewrite
it using a lemma. It uses `pathNatFromRel_adj`, which `@[simps!]` generated for
exactly this purpose. An `abbrev`, on the other hand, is unfolded by `simp`, and what
happens next depends on its body. The body of `pathNat` is a structure with its `Adj`
field written out, so `simp` reads `pathNat.Adj a b` straight off it, without using
any lemma at all. The body of `pathNatFromEdgeSet` is `fromEdgeSet s` for a set of
edges `s`, so `simp` sees `(fromEdgeSet s).Adj a b` and rewrites it with Mathlib's
lemma `fromEdgeSet_adj` (and then tidies up the result).

So `simp` never uses `pathNat_adj` or `pathNatFromEdgeSet_adj`. They are still useful
as named lemmas, for example with `rw` in the proofs above: `pathNatFromEdgeSet_adj`
states adjacency in a tidied-up form, whereas rewriting with `fromEdgeSet_adj` would
leave a goal about `Sym2`.

In fact Mathlib would not accept `pathNatFromEdgeSet_adj` as a `simp` lemma. If
another `simp` lemma also applies to the left-hand side of a `simp` lemma, then
`simp` may use that one instead, and the lemma never gets used. So the left-hand side
of a `simp` lemma should be in *simp normal form*: no other `simp` lemma should apply
to it. The left-hand side `pathNatFromEdgeSet.Adj a b` fails this test, since the
`simp` lemma `fromEdgeSet_adj` applies to it. Mathlib checks every `simp` lemma for
this with its `simpNF` linter, which you can run on your own file with
`#lint only simpNF`. We will meet simp normal forms again in [Copy](#section-copy).

`simp?` has a second use. The `simp` set grows as Mathlib does, so a plain `simp` may
do something different in a future version of Mathlib. That's fine if `simp` closes
the goal, but if later steps depend on exactly what `simp` produced then the proof
may break. So the convention in Mathlib is that a *non-terminal* `simp`, one that
does not close the goal, should be a `simp only`. Mathlib's `flexible` linter, which
is enabled for this guide, warns about a non-terminal `simp` (its warning calls
`simp` a *flexible* tactic) and suggests using `simp?`. For example, if `a + 1` and
`b + 1` are adjacent in `pathNat` then so are `a` and `b`, but the following proof of
this triggers the warning.
-/
/-- warning: `simp at h` is a flexible tactic modifying `h`. Try `simp?` -/
#guard_msgs (substring := true) in
example (a b : ℕ) (h : pathNat.Adj (a + 1) (b + 1)) : pathNat.Adj a b := by
  simp at h
  exact h

/-!
Following its advice and running `simp?` leads to a proof that does not depend on the
rest of the `simp` set.
-/
example (a b : ℕ) (h : pathNat.Adj (a + 1) (b + 1)) : pathNat.Adj a b := by
  simp only [Nat.add_right_cancel_iff] at h
  exact h

/-!
Often a neater fix is to let `simp` finish the proof. `simpa using e` simplifies both
the goal and the type of `e`, then closes the goal with `e` (and
`simpa [foo] using e` also rewrites with the lemma `foo`). Without the simplification
`exact h` would fail, since `h` and the goal only agree once both have been
simplified.
-/
example (a b : ℕ) (h : pathNat.Adj (a + 1) (b + 1)) : pathNat.Adj a b := by
  simpa using h

/-!
## Grind

`grind` is the other automated tactic we use throughout this guide, and it works
quite differently from `simp`. Rather than rewriting the goal, it assumes that the
goal is false and looks for a contradiction. Along the way it collects facts, keeps
track of which terms are equal, splits into cases, applies lemmas whenever it meets
terms that match them, and uses built-in procedures for linear arithmetic over `ℕ`
and `ℤ` and for algebra in commutative rings. It only ever finishes a goal: if it
cannot, it fails and lists the facts it had collected, which often shows what it was
missing.

`grind` does not use the `simp` set. Unlike `simp`, it always uses all the hypotheses
in the local context (so passing one, as in `grind [h]`, is an error). Apart from
these and its built-in reasoning, it only uses the lemmas tagged with a `grind`
attribute and those we pass to it, as in `grind [foo, bar]`. Very few of Mathlib's
lemmas about graphs are tagged for `grind`, which is why our `grind` calls often list
lemmas.

Like `simp`, `grind` unfolds an `abbrev` but not a `def`.
-/
example (x : ℕ) : pathNat.Adj x (x + 1) := by grind

example (x : ℕ) : pathNatFromRel.Adj x (x + 1) := by grind [pathNatFromRel_adj]

example (x : ℕ) : pathNatFromEdgeSet.Adj x (x + 1) := by
  grind [pathNatFromEdgeSet_adj]

/-!
Plain `grind` fails on the last two goals: it cannot see inside the `def`
`pathNatFromRel`. It does unfold the `abbrev` `pathNatFromEdgeSet`, but Mathlib's
`fromEdgeSet_adj` is not a `grind` lemma, so it is left with a set of edges in
`Sym2 ℕ` that it cannot work with. For the last goal `grind [fromEdgeSet_adj]` would
also work, but the tidied-up statement of `pathNatFromEdgeSet_adj` (the lemma that
`simp` never uses) is more useful in general. With it, `grind` proves that `pathNat`
and `pathNatFromEdgeSet` are equal without rewriting first, whereas
`grind [fromEdgeSet_adj]` fails here.
-/
example : pathNat = pathNatFromEdgeSet := by
  ext a b
  grind [pathNatFromEdgeSet_adj]

/-!
Like `simp?`, `grind?` suggests a call `grind only [...]` that uses just the lemmas
that were needed (it may also offer other forms of the call).
-/
example (x : ℕ) : pathNatFromRel.Adj x (x + 1) := by
  grind? [pathNatFromRel_adj] -- Try these: grind only [pathNatFromRel_adj], ...

/-!
Instead of passing a lemma to each `grind` call, we can tag it with a `grind`
attribute, so that every later `grind` call can use it. Most such tags in Mathlib are
`@[grind =]`, on equations or `↔`s characterizing a definition (like
`pathNatFromRel_adj`): `grind` then uses the lemma whenever it meets a term matching
its left-hand side. (Similarly `@[grind →]` uses an implication whenever it meets
terms matching its hypotheses.) Here we add the attribute for a single example only,
with `attribute [local grind =] … in`.
-/
attribute [local grind =] pathNatFromRel_adj in
example (x : ℕ) : pathNatFromRel.Adj x (x + 1) := by grind

/-!
Tags should be added sparingly, since they affect every later `grind` call, and a
lemma that matches too many terms can make `grind` slow. The command
`#grind_lint inspect foo` warns if the lemma `foo` leads `grind` into long chains of
lemma applications. In this guide we do not tag any lemmas for `grind`. Instead each
call lists the lemmas it needs, which also shows the reader which facts the proof
uses.

Finally, `grind` is not designed for problems that need a huge number of case splits,
such as checking by brute force that a particular graph has no `3`-colouring. For
finite checks like this we use `decide`, introduced in
[Decidability, Finiteness and Degrees](#chapter-decidability-finiteness-and-degrees).

# Computations

As well as reasoning about graphs in Lean we can also do computations with them. For
example we can check that `0` and `3` are adjacent in the complete graph on `Fin 5`
(the type consisting of `{0, 1, 2, 3, 4}`).
-/
#eval (⊤ : SimpleGraph (Fin 5)).Adj 0 3   -- true
/-!
We can count edges in finite graphs. For example the `completeGraph` on `Fin 6` has
`15` edges.
-/
#eval (⊤ : SimpleGraph (Fin 6)).edgeFinset.card -- 15
/-!
Even when our goal is to prove theorems, computations such as these can be very
useful. Firstly, they allow us to perform quick sanity checks of our definitions
and secondly they can be used inside proofs with the `decide` tactic.
-/
example : (⊤ : SimpleGraph (Fin 6)).Adj 2 3 := by decide

/-!
Both `#eval` and `decide` rely on adjacency being *decidable*: Lean needs a concrete
method for deciding whether or not any given pair of vertices are adjacent. We will
return to this, and to computations with graphs more generally, in
[Decidability, Finiteness and Degrees](#chapter-decidability-finiteness-and-degrees).
-/

end SimpleGraph
