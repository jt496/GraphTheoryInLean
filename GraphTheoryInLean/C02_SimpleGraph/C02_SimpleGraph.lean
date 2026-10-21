import GraphTheoryInLean.Common
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
namespace SimpleGraph
section basics
variable {V : Type*} (G : SimpleGraph V)
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
`loopless` that this relation is symmetric and irreflexive. Note that `V` is a
parameter of the structure rather than one of its fields: graphs on different vertex
types have different types. (We can omit proofs of `symm` and `loopless` and
Lean will try to fill them in using the automated `aesop_graph` tactic.)
-/
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
and `[Fintype V]`. See
[Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#chapter-decidability-finiteness-and-degrees)
for more details.

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

section darts
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
section order
/-!
# Order

There is a partial order on `SimpleGraph V` given by `G ≤ H` iff `G` is a subgraph of
`H`. (Note that these are necessarily spanning subgraphs since all `SimpleGraph V`
have the same vertex set. We will consider general subgraphs later, see
[Subgraphs](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#chapter-subgraphs).)

This gives `SimpleGraph V` the structure of a *complete atomic Boolean algebra*, with
operations `sup`, `inf`, `compl` and `sdiff`, and elements `top` and `bot`. This
terminology comes from order theory rather than graph theory, but it is very natural
in the context of formalization. Here *complete* means that every set of graphs in
`SimpleGraph V` has a supremum (the graph whose edges are those present in at least
one graph in the set) and an infimum (the graph whose edges are those present in
every graph in the set). The *atoms* of `SimpleGraph V` are the graphs with exactly
one edge, and *atomic* means that every graph is the supremum of the atoms below it,
i.e. the union of its single-edge subgraphs. Mathlib registers this structure as an
*instance*, which Lean supplies automatically wherever it is needed. The command
`#synth` asks Lean to find (synthesize) an instance and shows it; we say more about
instances in
[Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#chapter-decidability-finiteness-and-degrees).
-/
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
/-!
Notice that the last few proofs all made use of results about orders rather than
anything specific to graphs. They all follow easily from Mathlib's instance of
`CompleteAtomicBooleanAlgebra (SimpleGraph V)`, which we displayed with `#synth` at
the start of this section.
-/
end order
end basics
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
abbrev pathNat₁ : SimpleGraph ℕ where
  Adj x y := x + 1 = y ∨ y + 1 = x

/-!
The `@[simps]` attribute automatically generates the `simp` lemma `pathNat₁_adj`. An
*attribute*, written `@[…]` before a declaration, tells Lean to do something extra
with the declaration once it is defined: `@[simp]` registers a lemma for use by
`simp`, and `@[simps]` generates `simp` lemmas from a definition. (If you want to see
which lemmas are generated by a `@[simps]` attribute you can change it to `@[simps?]`
and the InfoView will tell you.)
-/
#check pathNat₁_adj -- pathNat₁.Adj x y = (x + 1 = y ∨ y + 1 = x)

/-!
Another way to construct the same graph is to use the `SimpleGraph.fromRel`
constructor which symmetrizes any given relation and removes loops (The
expression `(· + 1 = ·)` below is shorthand for the relation
`fun x y => x + 1 = y`.).
-/
#source SimpleGraph.fromRel

/-- The path graph on `ℕ` defined using `SimpleGraph.fromRel`. -/
@[simps!]
def pathNat₂ : SimpleGraph ℕ := SimpleGraph.fromRel (· + 1 = ·)

/-!
This time we used `@[simps!]` rather than `@[simps]`. Plain `@[simps]` reads its
lemmas straight off a definition written as a structure, as `pathNat₁` was (using
`where`), since the value of each field is written out explicitly. The body of
`pathNat₂` is instead an application of `fromRel`, so to find `Adj` the attribute
must first unfold `fromRel` and then tidy up the result with `simp`. The `!` asks for
both. (If we wrote `@[simps]` here, a linter warning would suggest `@[simps!]`.)
-/
#check pathNat₂_adj -- pathNat₂.Adj a b = (¬a = b ∧ (a + 1 = b ∨ b + 1 = a))

/-!
Also notice that `pathNat₂` is a `def`, whereas `pathNat₁` (and `pathNat₃` below) are
`abbrev`s, definitions that Lean unfolds automatically when it needs to. This is
deliberate: we will see in
[Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#chapter-decidability-finiteness-and-degrees)
how this choice affects Lean's ability to compute with these graphs.

These two graphs are equal, but not *definitionally* equal: `rfl` does not prove the
equality. We explain this important distinction in
[Definitional and Propositional Equalities](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-definitional-and-propositional-equalities)
below.

In order to prove that two `SimpleGraph`s are equal, we need to show that they have
the same adjacency relation (i.e. the same edges). We *don't* need to check that they
have the same vertex sets since this is done automatically by the type system: both
`pathNat₁` and `pathNat₂` are `SimpleGraph ℕ`.

Lean's type checker ensures that we can't even state a theorem saying that two graphs
with different vertex sets are equal. For example if `G : SimpleGraph V` then the
expression `G = pathNat₁` is not well-typed since `pathNat₁` has vertex type `ℕ` and
`G` has vertex type `V`. (The actual error is suppressed in the Lean source file
by the `#guard_msgs` command and only shown in the HTML version. Delete the
`#guard_msgs` line to see the error message in VS Code.)
-/
/-- error: Type mismatch
  pathNat₁
has type
  SimpleGraph.{0} ℕ -/
#guard_msgs (substring := true) in
example {V : Type*} (G : SimpleGraph V) : G = pathNat₁ := by
  sorry

/-!
Any two graphs on the same vertex type with the same edges are equal by
extensionality, and we can use the `ext` tactic to prove that `pathNat₁` and
`pathNat₂` are equal. The definition of `SimpleGraph` is tagged with the `@[ext]`
attribute which gives us the following `ext` lemmas for free.
-/
#check SimpleGraph.ext
#check SimpleGraph.ext_iff
/-!
The `ext` tactic reduces the goal to showing that for all `a` and `b`,
`pathNat₁.Adj a b ↔ pathNat₂.Adj a b`. After rewriting with the two adjacency
lemmas, what remains is a statement of logic and arithmetic about natural numbers,
which `grind` proves. `grind` is an automated tactic that combines case splitting,
congruence closure and linear arithmetic; we use it throughout this guide to finish
off goals of this kind.
-/

example : pathNat₁ = pathNat₂ := by
  ext a b
  -- now rewrite using the definition of adjacency in both graphs
  rw [pathNat₁_adj, pathNat₂_adj]
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
abbrev pathNat₃ : SimpleGraph ℕ := SimpleGraph.fromEdgeSet {e | ∃ n, e = s(n, n + 1)}

/-!
Again we can show that `pathNat₃` is equal to `pathNat₁` using `ext` (hence all three
definitions agree).
-/
lemma pathNat₁_eq_pathNat₃ : pathNat₁ = pathNat₃ := by
  ext a b
  rw [pathNat₁_adj, pathNat₃_adj]
  grind

/-!
We can also state this equality in terms of adjacency, which is usually more
convenient.
-/
lemma pathNat₁_adj_iff_pathNat₃ {x y : ℕ} : pathNat₁.Adj x y ↔ pathNat₃.Adj x y := by
  rw [pathNat₁_eq_pathNat₃]

/-!
## Definitional and Propositional Equalities

All three of our path graphs are equal, but Lean distinguishes two kinds of equality.
An equality `a = b` is *definitional* if both sides *unfold* to the same term, so
that `rfl` proves it; we then say that `a` and `b` are *definitionally equal*, or
*defeq* for short. Otherwise the equality is merely *propositional*: it may still be
true, but it needs a genuine proof. (Every definitional equality is also
propositional, with proof `rfl`.) The equality `pathNat₁ = pathNat₂` is propositional
but not definitional: we proved it with `ext` and a short argument about natural
numbers, while `rfl` fails.
-/
/-- error: Tactic `rfl` failed: The left-hand side
  pathNat₁
is not definitionally equal to the right-hand side
  pathNat₂ -/
#guard_msgs (substring := true) in
example : pathNat₁ = pathNat₂ := by rfl

/-!
Here *unfolding* means more than replacing names by their definitions: Lean also
*computes*, running any recursion or pattern match whose argument it can see is a
constructor. For example `+` on `ℕ` is defined by recursion on its second argument,
so `n + 0` computes to `n` even for a variable `n`, and `rfl` proves `n + 0 = n`. But
in `0 + n` the recursion is on the variable `n`, which is neither `0` nor a
successor, so the computation is *stuck*: `0 + n = n` is true, but only
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
example : (⊤ : SimpleGraph (Fin 6)).Adj 2 3 := by
  decide

/-!
Both `#eval` and `decide` rely on adjacency being *decidable*: Lean needs a concrete
method for deciding whether or not any given pair of vertices are adjacent. We will
return to this, and to computations with graphs more generally, in
[Decidability, Finiteness and Degrees](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#chapter-decidability-finiteness-and-degrees).
-/

end SimpleGraph
