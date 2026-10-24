import GraphTheoryInLean.Common
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Digraph.Basic
namespace SimpleGraph
/-!
Our goal in writing this guide is to introduce graph theorists to the interactive
proof assistant [Lean](https://lean-lang.org/) and its associated library
[Mathlib](https://leanprover-community.github.io/).

We don't aim to give a comprehensive introduction to Lean for mathematicians: there
are many excellent tutorials and texts for this, including:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
(the definitive introduction to Lean for mathematicians)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
(introduction to interactive theorem proving with dependent types using Lean)
- [A Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean/) ("an
introduction to theorem proving in Lean for the impatient")
- [The Hitchhiker’s Guide to Logical Verification](https://github.com/lean-forward/logical_verification_2025)
(companion text to a graduate-level course on interactive theorem proving)
- [How To Prove It With Lean](https://djvelleman.github.io/HTPIwL/) (an introduction
to proofs in Lean based on the classic textbook)
- [Logic and Proof](https://leanprover-community.github.io/logic_and_proof/) (a
course in logic and proof using Lean)
- [Lean Game Portal](https://adam.math.hhu.de/)
(interactive games such as the Natural Number Game)

A first course in graph theory is assumed, as is a basic level of Lean proficiency
(for example the first few chapters of
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)).

Our aim is to give graph theorists an idea of how formalizing their work might look
in Lean, making use of Mathlib. In particular we will try to point out the
differences that we encounter in Lean, compared to informal definitions and proofs.

# Installation

If you haven't done so already please [install Lean](https://lean-lang.org/install/)
and clone a copy of the repository <https://github.com/jt496/GraphTheoryInLean>.

# How to Read This Guide

If you are reading the `.lean` files directly in VS Code or similar then see the
`README.md` file for build instructions (`lake exe cache get` followed by
`lake build`). Each chapter is in a separate folder that also contains any associated
exercises.

If you are reading the web version then please note that this is published using
[Verso](https://verso.lean-lang.org/). You should be able to see most of the
interactive features of Lean such as InfoView messages and `#command` outputs.

To see the actual output of a `#command` you need to hover over the `#command` itself
with your cursor (the `#command` will have wavy underlining). Many terms also have
associated doc-strings which you can see by hovering over them; click on them to view
the full documentation. Types of terms are also shown.

For example, below you should be able to hover over the `#source` command to see the
verbatim source code of the definition of `SimpleGraph` in Mathlib. While if you
hover over `SimpleGraph` itself you will see its doc-string; clicking on it will take
you to its documentation page. Hovering over the `#check` will tell you the type of
`G.Adj u v` (it is a `Prop`), while hovering over `u` will confirm that it has type
`V`, which in turn you can hover over to see its type `Type u_1`.
-/
variable {V : Type*} {G : SimpleGraph V} (u v : V)
#source SimpleGraph
#check G.Adj u v -- Prop
#check sum_degrees_eq_twice_card_edges -- ∑ v, G.degree v = 2 * G.edgeFinset.card

/-!
Throughout this guide we work in the `namespace SimpleGraph`, so for example `Adj`
means `SimpleGraph.Adj`, and our definitions get names like `SimpleGraph.pathNat₁`.
When we want to put results or definitions in other namespaces we will do this
explicitly.

In the interest of making this guide as readable as possible by graph theorists we
introduce quite a lot of "standard" graph theory notation that is not in Mathlib (for
example `K[n]`, `C[n]`, `K[s, t]`, `Q[n]`, `ω G`, `χ G`, etc.). For reference, see
[Notation](#section-notation). We also provide lists of the
[Definitions](#section-definitions) introduced in the guide and of the main
[Results](#section-results) proved in it.

# Finding Lemmas

Much of the work of formalizing is finding the right lemma in Mathlib. Mathlib's
naming conventions (see [Naming Conventions](#section-naming-conventions)) help,
since a name should describe the statement (for example
`card_neighborFinset_eq_degree`), but they only get you so far: the degree of a
vertex in a complete graph is `complete_graph_degree`, not `degree_top`. So it is
worth knowing how to search.

* The tactic `exact?` searches Mathlib for a lemma that closes the current goal, and
  `apply?` and `rw?` do the same for `apply` and `rw`.
* [Loogle](https://loogle.lean-lang.org/) searches by constants and expressions, for
  example `SimpleGraph.degree` and `SimpleGraph.completeGraph`.
* [LeanSearch](https://leansearch.net/) searches using natural language, for example
  "degree of a vertex in the complete graph".
* Mathlib's documentation pages list the declarations of each file in order, so the
  lemmas about a definition can usually be found near it.

# How This Guide is Structured

This guide is focused entirely on `SimpleGraph`. We start with the basic definitions
in the next chapter before moving on to give many different concrete examples in
[Constructions](#chapter-constructions). The following chapter, [Decidability,
Finiteness and Degrees](#chapter-decidability-finiteness-and-degrees), shows how to
compute with graphs and introduces vertex degrees.

The rest of the guide introduces topics mainly according to dependencies in Mathlib:
[Maps](#chapter-maps), [Cliques](#chapter-cliques), [Colorings](#chapter-colorings),
[Walks](#chapter-walks), [Subgraphs](#chapter-subgraphs),
[Connectivity](#chapter-connectivity), [Distance](#chapter-distance), [Algebraic
Graph Theory](#chapter-algebraic-graph-theory), before looking at some of the
classical [Theorems](#chapter-theorems) about graphs in Mathlib.

After [Maps](#chapter-maps) the guide splits into two strands that can be read
in either order: [Cliques](#chapter-cliques) and
[Colorings](#chapter-colorings) on the one hand, and
[Walks](#chapter-walks) on the other. The strands meet in
[Subgraphs](#chapter-subgraphs), and from there each chapter builds on the
previous ones.

Most chapters begin with a few basic sections before moving on to more involved
material. Sections or subsections whose titles are marked with a star are more
advanced. Later sections sometimes use their results, and recall what they need when
they do.

[Figure: A route through the guide](https://jt496.github.io/GraphTheoryInLean/figures/reading_routes.svg)

We use three running examples throughout: the `n`-dimensional hypercube `Q[n]`
([Hypercube](#section-hypercube)), the Mycielskian `mμ[G]` of a graph `G`
([Mycielskian](#section-mycielskian)), and the infinite path `pathNat₁` on `ℕ`
([Constructing a SimpleGraph](#section-constructing-a-simplegraph)).

Examples of more advanced topics that we cover in the guide include:

* [Graphic Sequences](#section-graphic-sequences)
* [Independence Number of the Kneser
  Graph](#section-independence-number-of-the-kneser-graph)
* [Colouring Mycielskians](#section-colouring-mycielskians)
* [Greedy Colouring](#section-greedy-colouring)
* [Pósa Rotations](#section-p-sa-rotations)
* [Bondy–Chvátal Theorem](#section-the-bondy-chv-tal-theorem)
* [De Bruijn–Erdős Theorem](#section-de-bruijn-erd-s-theorem)
* [Vertex Connectivity](#section-vertex-connectivity)
* [Brooks' Theorem](#section-brooks-theorem)
* [Cut Vertices and Blocks](#section-cut-vertices-and-blocks)
* [Moore and Cage Bounds](#section-moore-and-cage-bounds)
* [Albertson's Precolouring Extension
  Theorem](#section-albertson-s-precolouring-extension-theorem)
* [Counting Copies](#section-counting-copies)
* [The Automorphism Group of the
  Hypercube](#section-the-automorphism-group-of-the-hypercube)
* [Kőnig's Theorem](#section-k-nig-s-theorem)
* [Füredi's Stability Theorem](#section-f-redi-s-stability-theorem)
* [Zykov's Theorem](#section-zykov-s-theorem)
* [Ruzsa–Szemerédi Theorem](#section-the-ruzsa-szemer-di-theorem)

Theorems from Mathlib that we survey, mostly in the final chapter
[Theorems](#chapter-theorems), include:

* [Hall's Marriage Theorem](#section-hall-s-marriage-theorem)
* [Tutte's Theorem](#section-tutte-s-theorem)
* [Turán's Theorem](#section-tur-n-s-theorem) and
  [Mantel's Theorem](#section-mantel-s-theorem)
* [Andrásfai–Erdős–Sós Theorem](#section-andr-sfai-erd-s-s-s-theorem)
* [Erdős–Stone Theorem](#section-tur-n-density-and-the-erd-s-stone-theorem)
* [The Laplacian](#section-the-laplacian)
* [Strongly Regular Graphs](#section-strongly-regular-graphs)
* [Szemerédi Regularity Lemma](#section-the-szemer-di-regularity-lemma)
* [Triangle Removal Lemma](#section-the-triangle-removal-lemma) and
  [Roth's Theorem](#section-roth-s-theorem)
* [Kőnig's Lemma](#section-k-nig-s-lemma) and [Ends](#section-ends)

Each chapter (except this one) has some exercises with worked solutions. Each set of
exercises is given first with `sorry`, and the solutions follow.

Since we want to develop results for our running examples some of these exercises are
named lemmas or theorems rather than anonymous examples. To avoid naming clashes we
add a prime (`foo'`) to the versions with `sorry`.
-/
end SimpleGraph
