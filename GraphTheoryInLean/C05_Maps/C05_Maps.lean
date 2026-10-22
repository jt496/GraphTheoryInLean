import GraphTheoryInLean.C04_Decidability_Finiteness_and_Degrees.Exercises
import Mathlib.Combinatorics.SimpleGraph.Acyclic -- also supplies `IsAcyclic` to C07 and C10
namespace SimpleGraph
/-!
Maps, in particular graph homomorphisms, are a fundamental concept in graph theory
but they are often glossed over in informal treatments. In Lean they play a much more
central role. For example, to say that a graph contains an induced `5`-cycle we need
to talk about embeddings of `C[5]` into the graph. Underlying this is the fact that
any `SimpleGraph V` has a fixed vertex type `V`, so to even express the idea that a
graph `G` contains a copy of `H`, when `G` and `H` have different vertex types,
requires the use of a map.

In this chapter we will study mappings between graphs. We first review functions,
embeddings, and equivalences of types, and then the construction `SimpleGraph.comap`,
which pulls a graph back along a function (it is used to define induced subgraphs).
Next we introduce graph homomorphisms (`→g`), graph embeddings (`↪g`), and graph
isomorphisms (`≃g`), together with `SimpleGraph.Copy`, the type of injective graph
homomorphisms. We then look at `SimpleGraph.map`, which pushes a graph forward along
a function, and at the natural maps associated with our running examples, the
hypercube and the Mycielskian. Next we use graph automorphisms to define
vertex-transitivity, a notion that recurs throughout the guide.

The chapter ends with two more advanced sections, on the tensor product of graphs
and on claw-free graphs, where we characterize when the line graph of a graph
contains a triangle.

# Functions, Embeddings and Equivalences

The basic function type in Mathlib is `V → W`, but we also have the embedding type
`V ↪ W` for injective functions and the equivalence type `V ≃ W` for equivalences
(bijections). Both are *bundled*: a term of each type is a structure packaging a
function (or in the case of an equivalence, a function and its inverse) together with
proofs of the properties it is required to have.

An *embedding* consists of a function together with a proof that it is injective.
-/
section functions
variable {V W X : Type*}

#source Function.Embedding

example (f : V ↪ W) : Function.Injective f := f.injective
/-!
The identity function as an embedding.
-/
example : V ↪ V := Function.Embedding.refl V
/-!
We can compose embeddings using `.trans`.
-/
example (f : V ↪ W) (g : W ↪ X) : V ↪ X := f.trans g
/-!
An *equivalence* is not simply a bijective function: it is a pair of functions
together with proofs that they are left/right inverses of each other.
-/
#source Equiv
/-!
Any equivalence is a bijection.
-/
example (e : V ≃ W) : Function.Bijective e := e.bijective
/-!
Conversely, `Equiv.ofBijective` turns a bijective function into an equivalence, but
it is `noncomputable`: for each `w : W` the inverse has to *choose* some `v` with
`f v = w`, and a proof of surjectivity only tells us that such a `v` exists.
-/
noncomputable example (f : V → W) (hf : Function.Bijective f) : V ≃ W :=
  Equiv.ofBijective f hf
/-!
The inverse of an equivalence `e` is `e.symm`.
-/
example (e : V ≃ W) : W ≃ V := e.symm
/-!
Examples of equivalences include the identity equivalence and the equivalence that
swaps two given elements of a type.
-/
example : V ≃ V := Equiv.refl V
example (u v : V) [DecidableEq V] : V ≃ V := Equiv.swap u v
/-!
Equivalences can be composed using `.trans`.
-/
example (e : V ≃ W) (f : W ≃ X) : V ≃ X := e.trans f
/-!
Given embeddings `V ↪ W` and `W ↪ V` the Cantor–Schröder–Bernstein theorem says that
there exists an equivalence `V ≃ W`. Its proof is non-constructive, so Mathlib states
it as `Nonempty (V ≃ W)`, a proposition saying that an equivalence exists, rather
than as a definition producing the equivalence itself, which would be data. (Compare
`Finite` and `Fintype` in
[Finiteness Without Data: the Finite Typeclass](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-finiteness-without-data-the-finite-typeclass).)
-/
example (f : V ↪ W) (g : W ↪ V) : Nonempty (V ≃ W) :=
  Function.Embedding.antisymm f g

end functions
/-!
# Comaps

Given a function `f : V → W`, we can push a graph `G : SimpleGraph V` forwards along
`f` or pull a graph `H : SimpleGraph W` back along `f`. The former is called the
*map* of `G` along `f` and the latter is called the *comap* of `H` along `f`.

Of these, `SimpleGraph.comap` is used frequently in constructions of concrete graphs,
so we start with it. The `SimpleGraph.map` construction is less frequently used for
constructing concrete graphs, but appears often in proofs; we return to it in
[Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#section-maps), once we have
met graph homomorphisms.

Given `f : V → W` and `G : SimpleGraph W`, `G.comap f` is the `SimpleGraph V` where
two vertices are adjacent iff their images under `f` are adjacent in `G`.

[Figure: $G$ (right) pulled back back along $f : V \to W$ (dashed arrows), to give `G.comap f` (left)](https://jt496.github.io/GraphTheoryInLean/figures/comap.svg)
-/
#source SimpleGraph.comap
example {V W : Type*} (f : V → W) {v₁ v₂ : V} (G : SimpleGraph W) :
  (G.comap f).Adj v₁ v₂ ↔ G.Adj (f v₁) (f v₂) := comap_adj ..

/-!
Two examples of graphs defined using `comap` are the complete multipartite and
blow-up graphs. (If you read the starred section
[Complete Multipartite Graphs and Blow-ups*](https://jt496.github.io/GraphTheoryInLean/Constructions/#section-complete-multipartite-graphs-and-blow-ups),
you have already seen them.) Two vertices are adjacent in a complete multipartite
graph iff they are in different parts.
-/
#source completeMultipartiteGraph    -- SimpleGraph (Σ i, V i) := .comap Sigma.fst ⊤
example {ι : Type*} (V : ι → Type*) {u v : Σ i, V i} :
    (completeMultipartiteGraph V).Adj u v ↔ u.fst ≠ v.fst := Iff.rfl

/-!
Two vertices are adjacent in the blow-up of a graph `G` iff they are in parts that
are adjacent in `G`.
-/
#source blowUpGraph -- abbrev blowUpGraph {ι : Type*} (G : SimpleGraph ι)
                    --    (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
                    --                          SimpleGraph.comap Sigma.fst G

example {ι : Type*} (V : ι → Type*) {u v : Σ i, V i} (G : SimpleGraph ι) :
    (G.blowUpGraph V).Adj u v ↔ G.Adj u.fst v.fst := Iff.rfl

/-!
In both cases the adjacency relation is defined by pulling back the adjacency
relation of a graph using `SimpleGraph.comap` and the map `Sigma.fst : Σ i, V i → ι`
that sends a vertex to its part.

## Induced Subgraphs via Comap

The `comap` gives a natural way to define induced subgraphs (`SimpleGraph.induce`).
Given a set of vertices `s : Set V`, the embedding of `s` into `V` as a `Subtype` is
given by `Function.Embedding.subtype (· ∈ s)`.
-/
section induced
variable {V : Type*} {s : Set V}
#check Function.Embedding.subtype (· ∈ s) -- {x // x ∈ s} ↪ V
/-!
The induced subgraph of `G` on the vertex set `s` is then given by the `comap` of `G`
by this embedding.

[Figure: Left: a graph $G$ with a subset $s$ of its vertices. Right: the induced subgraph on $s$](https://jt496.github.io/GraphTheoryInLean/figures/induced.svg)
-/
#source induce -- abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
               --                   G.comap (Function.Embedding.subtype _)

#check SimpleGraph.induce_adj --  (induce s G).Adj u v ↔ G.Adj ↑u ↑v
#check SimpleGraph.induce s   -- induce s : SimpleGraph V → SimpleGraph ↑s
/-!
Notice that `G.induce s` gives a `SimpleGraph ↑s` whose vertices have a different
type to those of the original graph. So for example in the subgraph of `C[5]` induced
by the set `{0, 1, 2}` the vertices are of type `↑{0, 1, 2}`. So when talking about
vertices in this graph we need to provide a pair `⟨v, hv⟩` where `v : Fin 5` and
`hv : v ∈ {0, 1, 2}`. Often these proof obligations can be discharged automatically
using `by simp` or `by decide`. (Either will work in the example below.)
-/
example : (C[5].induce {0, 1, 2}).Adj ⟨0, by simp⟩ ⟨1, by decide⟩ := by decide

/-!
In the subgraph of the path on `ℕ` induced by even natural numbers, no two
(necessarily even) vertices are adjacent.
-/
example {a b : {n : ℕ // Even n}} : ¬ (pathNat₁.induce {n | Even n}).Adj a b := by
  rw [induce_adj, pathNat₁_adj]
  grind

example {a b : ℕ} :
    ¬ (pathNat₁.induce {n | Even n}).Adj ⟨2 * a, by simp⟩ ⟨2 * b, by simp⟩ := by
  rw [induce_adj, pathNat₁_adj]
  -- ⊢ ¬ (↑⟨2 * a, ⋯⟩ + 1 = ↑⟨2 * b, ⋯⟩ ∨ ↑⟨2 * b, ⋯⟩ + 1 = ↑⟨2 * a, ⋯⟩)
  grind

/-!
If you want a subgraph whose vertices have type `V` but containing only the vertices
in `s` (which is often a more useful definition of an induced subgraph) then you need
to use the `Subgraph` type (see
[Subgraphs](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#chapter-subgraphs)
for details).
-/
variable {G : SimpleGraph V}
#check ((⊤ : G.Subgraph).induce s)
end induced

/-!
# Morphisms

Graph homomorphisms, embeddings, and isomorphisms are the structure-preserving maps
between graphs. Unlike `comap`, which takes a plain function and builds a new graph,
a morphism is *data* relating two given graphs: a function between their vertex types
together with a proof that it respects adjacency. We will see below how the two ideas
are related.

Before looking at morphisms in detail we note that they are all defined as `abbrev`s
for the corresponding `Rel*` types in Mathlib. This means that occasionally when
working with these maps we will use results that refer to `RelHom`, `RelEmbedding` or
`RelIso`.

[Figure: Left: a homomorphism from $C_4$ onto $K_2$, identifying opposite vertices. Centre: an embedding of a path. Right: an isomorphism](https://jt496.github.io/GraphTheoryInLean/figures/homembed.svg)

## Graph Homomorphisms
-/

section hom
variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
/-!
A *graph homomorphism* from `G` to `H` is a map between vertex types sending edges to
edges. In Mathlib this is called `SimpleGraph.Hom G H` and written `G →g H`.
Homomorphisms preserve adjacency.
-/
example (f : G →g H) (u v : V) (h : G.Adj u v) : H.Adj (f u) (f v) := f.map_adj h
/-!
The identity as a graph homomorphism:
-/
#check Hom.id   -- G →g G
/-!
We can compose homomorphisms.
-/
example (g : H →g K) (f : G →g H) : G →g K := g.comp f
/-!
If `G₁ ≤ G₂` then there is an associated homomorphism `G₁ →g G₂` given by the
identity function on vertices.
-/
#check Hom.ofLE --  {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) : G₁ →g G₂
/-!
A homomorphism maps neighbourhoods into neighbourhoods.
-/
example (f : G →g H) (v : V) : (G.neighborSet v).image f ⊆ H.neighborSet (f v) := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := hw
  exact f.map_adj hu

/-!
We can now relate homomorphisms to `comap`. A function `f : V → W` underlies a
homomorphism `G →g H` iff `G` is a subgraph of `H.comap f`: both say that `f` sends
every edge of `G` to an edge of `H`.
-/
example (f : G →g H) : G ≤ H.comap f := f.le_comap
example (f : V → W) (h : G ≤ H.comap f) : G →g H := ⟨f, fun huv ↦ h huv⟩
/-!
In particular, taking `G` to be `H.comap f` itself, `f` is always a homomorphism
`H.comap f →g H`. Mathlib calls this `Hom.comap`.
-/
#check Hom.comap -- (f : V → W) (G : SimpleGraph W) : G.comap f →g G
/-!
Any graph homomorphism from the complete graph `⊤` is injective.
-/
#check Hom.injective_of_top_hom
/-!
Homomorphisms into a complete graph are also important. A homomorphism
`G →g (⊤ : SimpleGraph γ)` sends adjacent vertices of `G` to distinct elements of
`γ`, so it is exactly a proper colouring of `G` with colours from `γ`. Indeed this is
how Mathlib defines `G.Coloring γ` (see
[Colorings](https://jt496.github.io/GraphTheoryInLean/Colorings/#chapter-colorings)).
Composing with a homomorphism `G →g H` turns colourings of `H` into colourings of
`G`, so if `H` is `n`-colourable then so is `G`.
-/
example (γ : Type*) : G.Coloring γ = (G →g (⊤ : SimpleGraph γ)) := rfl
#check Colorable.of_hom -- (f : G →g G') : G'.Colorable n → G.Colorable n

end hom

/-!
## Graph Embeddings
-/
section embed
variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
         (f : G ↪g H) (g : H ↪g K)
/-!
A `SimpleGraph.Embedding G H`, written `G ↪g H`, is an embedding `V ↪ W` (i.e. an
injective map) such that `∀ u v, G.Adj u v ↔ H.Adj (f u) (f v)`. In other words, `f`
is an injective homomorphism that also *reflects* edges:
`H.Adj (f u) (f v) → G.Adj u v`. This means that `G` is isomorphic to an induced
subgraph of `H`.
-/
example {u v : V} : H.Adj (f u) (f v) ↔ G.Adj u v := f.map_adj_iff

/-!
In terms of `comap`: an injective function `f` underlies an embedding `G ↪g H` iff
pulling back `H` along `f` gives exactly `G`. Conversely, `comap` along any injective
function is an embedding (`Embedding.comap`), and a special case of this is the
inclusion of an induced subgraph (`Embedding.induce`).
-/
example : H.comap f = G := f.comap_eq
#check Embedding.comap  -- (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G
#check Embedding.induce -- (s : Set V) : G.induce s ↪g G

/-!
Graph embeddings compose. (We can write this in two superficially different ways; the
second makes use of the fact that `SimpleGraph.Embedding` is an `abbrev` for
`RelEmbedding`.)
-/
#check g.comp f  -- G ↪g K
#check f.trans g -- RelEmbedding.trans f g : G.Adj ↪r K.Adj
example : g.comp f = f.trans g := rfl

/-!
Every graph embedding gives rise to a homomorphism and an underlying embedding of
vertex types.
-/
#check Embedding.toHom  -- .. (f : G ↪g G') : G →g G'
#check f.toEmbedding    -- V ↪ W

end embed

/-!
Recall `pathNat₁`, the path graph on `ℕ`. We can embed this in itself by sending `i`
to `i + j`, for any fixed `j : ℕ`.
-/
#source pathNat₁

/-- The graph embedding `pathNat₁ ↪g pathNat₁`, with `i ↦ i + j`. -/
@[simps]
def pathNat₁Translate (j : ℕ) : pathNat₁ ↪g pathNat₁ where
  toFun i := i + j
  inj' := add_left_injective j
  map_rel_iff' := by grind [Function.Embedding.coeFn_mk]

/-!
We can embed `G` into any blow-up `G.blowUpGraph W` so long as the parts of the
blow-up are nonempty (the argument `f` below picks an element of each part).
-/
/-- Embedding of `G` into `G.blowUpGraph W` with nonempty parts. -/
@[simps]
def Embedding.blowUp {ι : Type*} (G : SimpleGraph ι) (W : ι → Type*)
    (f : (i : ι) → W i) : G ↪g (G.blowUpGraph W) where
  toFun i := ⟨i, f i⟩
  inj' _ _ h := congrArg Sigma.fst h
  map_rel_iff' := Iff.rfl

/-!
For example, here is the embedding of `C[4]` into its blow-up with all parts equal to
`Fin 3`, sending each vertex `i : Fin 4` of `C[4]` to the vertex `⟨i, 0⟩` of the
blow-up.
-/
#check (Embedding.blowUp C[4] (fun _ => (Fin 3)) (fun _ => 0))

/-!
## Copies

We already met graph homomorphisms `A →g B` and graph embeddings `A ↪g B`. `Copy A B`
falls between the two: it is the type of injective graph homomorphisms from `A` to
`B`.

While `A ↪g B` captures the type of *induced* copies of a graph `A` in a graph `B`,
`Copy A B` captures the type of *not-necessarily-induced* copies of `A` in `B`.
-/
#source Copy
/-!
Note that the copies are *labelled*: an element of `Copy A B` records where each
vertex of `A` goes. So if `A` has nontrivial automorphisms then a single subgraph of
`B` isomorphic to `A` is the image of several elements of `Copy A B`, one for each
automorphism of `A`. We return to this distinction in
[Counting Copies*](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-counting-copies).

An induced copy of `A` in `B` (i.e. `f : A ↪g B`) gives rise to a copy of `A` in
`B`.
-/
#source Embedding.toCopy -- .. (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective
/-!
Note that any copy of a complete graph is necessarily induced, so we can always
upgrade a `Copy ⊤ G` to a graph embedding `⊤ ↪g G`.
-/
example {V W : Type*} {G : SimpleGraph V} (c : Copy (⊤ : SimpleGraph W) G) :
    (⊤ : SimpleGraph W) ↪g G := c.topEmbedding

/-!
We say that `A` is *contained* in `B`, written `A.IsContained B` or `A ⊑ B`, iff
there exists a `Copy A B`.
-/
#source IsContained -- (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (Copy A B)
/-!
If `B` contains no copy of `A` then we say that `B` is `A`-*free*, written
`A.Free B`. This follows the convention of extremal graph theory, where "`A`-free"
means containing no copy of `A` at all (as in "triangle-free"). Beware that
structural graph theory often uses "`A`-free" to mean containing no *induced* copy of
`A` (as in "claw-free"). For that notion we need a separate definition, which we give
in
[Claw-Free Graphs*](https://jt496.github.io/GraphTheoryInLean/Maps/#section-claw-free-graphs).
-/
#source Free -- abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B

/-!
## Graph Isomorphisms
-/
section iso
variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
         (f : G ≃g H) (g : H ≃g K)
/-!
A `SimpleGraph.Iso G H`, written `G ≃g H`, is a graph isomorphism, i.e. it is an
equivalence of vertex types that respects adjacency.
-/
#check Iso
/-!
The identity isomorphism:
-/
#check Iso.refl  -- G ≃g G
/-!
The inverse of an isomorphism is an isomorphism.
-/
#check Iso.symm  -- G ≃g H → H ≃g G
/-!
Isomorphisms compose:
-/
#check g.comp f -- G ≃g K
/-!
The underlying equivalence of vertex types:
-/
#check f.toEquiv  -- V ≃ W
/-!
Any graph isomorphism gives rise to a graph embedding or graph homomorphism.
-/
#check Iso.toEmbedding  -- G ≃g G' → G ↪g G'
#check Iso.toHom        -- G ≃g G' → G →g G'

/-!
Isomorphic graphs have the same graph-theoretic invariants. For example, an
isomorphism preserves the degree of each vertex, the minimum and maximum degree, and
the number of edges.
-/
#check Iso.degree_eq          -- (f : G ≃g G') (x : V) : G'.degree (f x) = G.degree x
#check Iso.minDegree_eq       -- (f : G ≃g G') : δ(G) = δ(G')
#check Iso.maxDegree_eq       -- (f : G ≃g G') : Δ(G) = Δ(G')
#check Iso.card_edgeFinset_eq -- (f : G ≃g G') : #G.edgeFinset = #G'.edgeFinset
/-!
Informally, "isomorphic graphs have the same properties" is a single meta-theorem
that we use without comment. In Lean there is no such meta-theorem: every invariant
needs its own transfer lemma, which is why Mathlib contains many lemmas of the form
`Iso.*_eq` and `Iso.*_iff`. Here are some for notions we meet later: connectedness
and acyclicity
([Connectivity](https://jt496.github.io/GraphTheoryInLean/Connectivity/#chapter-connectivity))
and the chromatic number
([Colorings](https://jt496.github.io/GraphTheoryInLean/Colorings/#chapter-colorings)).
-/
#check Iso.connected_iff  -- G ≃g H → (G.Connected ↔ H.Connected)

#check Iso.isAcyclic_iff  -- G ≃g H → (G.IsAcyclic ↔ H.IsAcyclic)

example (e : G ≃g H) : G.chromaticNumber = H.chromaticNumber :=
  chromaticNumber_congr e

/-!
Equivalences of types induce isomorphisms of complete graphs on those types.
-/
#check Iso.completeGraph

/-!
The analogous fact for empty graphs is also true, but not supplied by Mathlib, so we
give it here.
-/
/-- Equivalences of types induce isomorphisms of empty graphs on those types. -/
protected def Iso.emptyGraph {α β : Type*} (f : α ≃ β) :
    emptyGraph α ≃g emptyGraph β where
  __ := f
  map_rel_iff' := by simp

end iso
/-!
## Coercions to Functions

Graph homomorphisms, embeddings and isomorphisms are not simply functions. A
homomorphism `f : G →g H` is a structure bundling a function `f.toFun : V → W` with
the proof `f.map_rel'` that it preserves adjacency, and embeddings and isomorphisms
are structures in the same way (as are `V ↪ W` and `V ≃ W` from the first section).
Nevertheless we have been writing `f v` for the image of a vertex throughout. This
works because Mathlib registers a `FunLike` instance for each of `G →g H`, `G ↪g H`
and `G ≃g H`, which lets Lean insert a *coercion* to a function whenever a map is
applied to an argument. The InfoView marks a coerced map with an arrow, `⇑f`.
-/
section coe
variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
         (f : G →g H) (g : H →g K) (e : G ↪g H) (φ : G ≃g H)

#check fun v => f v   -- fun v ↦ f v : V → W
set_option pp.coercions false in
#check fun v => f v   -- fun v ↦ DFunLike.coe f v : V → W
/-!
The coercion is definitionally the underlying function, and composing maps composes
the coerced functions (`Hom.coe_comp` and its analogues). Note that `g.comp f` is not
literally `g ∘ f`: in the latter Lean coerces the two homomorphisms to functions and
composes those. The two are equal as functions, but only `g.comp f` is a
homomorphism.
-/
example : (f : V → W) = f.toFun := rfl
example : ⇑(g.comp f) = g ∘ f := rfl
/-!
Since each kind of map is determined by its function, two maps of the same kind are
equal if they agree on every vertex (by *extensionality*).
-/
example (f₁ f₂ : G →g H) (h : ∀ v, f₁ v = f₂ v) : f₁ = f₂ := DFunLike.ext _ _ h
example (φ₁ φ₂ : G ≃g H) (h : ∀ v, φ₁ v = φ₂ v) : φ₁ = φ₂ := DFunLike.ext _ _ h
/-!
Likewise, properties of functions are properties of the coerced function:
`Function.Injective e` means `Function.Injective ⇑e`, and Mathlib supplies the
expected facts (via `RelEmbedding.injective`, `RelIso.bijective`, and so on).
-/
example : Function.Injective e := e.injective
example : Function.Bijective φ := φ.bijective

end coe

/-!
# Maps

Given any function `f : V → W` we can form the *map* of a graph `G : SimpleGraph V`
along `f`. This gives a graph `G.map f : SimpleGraph W` on the vertex set `W` where
two vertices are adjacent iff they are distinct and are the images of adjacent
vertices in `G`. The distinctness condition is needed because `f` need not be
injective: if `f` sends two adjacent vertices to the same vertex then their edge
would otherwise become a loop.

[Figure: $G$ (left) pushed forward along $f : V \to W$ (dashed arrows), to give `G.map f` (right)](https://jt496.github.io/GraphTheoryInLean/figures/map.svg)
-/
variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}

#source SimpleGraph.map

example (f : V → W) {w₁ w₂ : W} (G : SimpleGraph V) :
    (G.map f).Adj w₁ w₂ ↔ w₁ ≠ w₂ ∧ ∃ v₁ v₂, G.Adj v₁ v₂ ∧ f v₁ = w₁ ∧ f v₂ = w₂ :=
  Iff.rfl
/-!
When `f : V ↪ W` is an embedding the distinctness condition is automatic, and
Mathlib's `map_adj` omits it.
-/
example (f : V ↪ W) {w₁ w₂ : W} (G : SimpleGraph V) :
  (G.map f).Adj w₁ w₂ ↔ ∃ v₁ v₂, G.Adj v₁ v₂ ∧ f v₁ = w₁ ∧ f v₂ = w₂ := map_adj ..
/-!
Either way, the adjacency relation of `G.map f` contains an existential quantifier:
two vertices are adjacent if there *exist* adjacent preimages. This makes graphs
defined using `map` harder to work with, particularly in computations.

How does `map` relate to homomorphisms? The image of `G` under a homomorphism
`f : G →g H` is a subgraph of `H` (`Hom.map_le`). For an embedding of vertex types
`f : V ↪ W` the converse also holds, so in that case `G.map f ≤ H` and
`G ≤ H.comap f` both say that `f` is a homomorphism `G →g H`.
-/
example (f : G →g H) : G.map f ≤ H := f.map_le
example (f : V ↪ W) : G.map f ≤ H ↔ G ≤ H.comap f := map_le_iff_le_comap
/-!
For a function that is not injective the converse fails: `map` may send two adjacent
vertices to the same vertex, so `G.map f ≤ H` does not ensure that `f` sends every
edge of `G` to an edge of `H`.

In the language of order theory, `map_le_iff_le_comap` says that `map f` and
`comap f` form a *Galois connection* when `f` is an embedding. It is in fact a
*Galois coinsertion*: mapping forwards and then pulling back recovers the original
graph, while pulling back and then mapping forwards only gives a subgraph. (See the
exercises for an example where this inequality is strict.)
-/
example (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := comap_map_eq ..
example (f : V ↪ W) (H : SimpleGraph W) : (H.comap f).map f ≤ H := map_comap_le ..
/-!
Mathlib also packages `map` as morphisms: an embedding `f : V ↪ W` gives a graph
embedding `G ↪g G.map f`, and an equivalence `e : V ≃ W` gives a graph isomorphism
`G ≃g G.map e`.
-/
#check Embedding.map -- (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f
#check Iso.map       -- (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f

/-!
## SpanningCoe

Having defined induced subgraphs via `comap` we can also go in the other direction:
starting with `G : SimpleGraph ↑s`, where `s : Set V`, we can use `SimpleGraph.map`
and `Subtype s ↪ V` to get a `SimpleGraph V` whose edges are exactly those of `G`.
Since this graph contains all vertices of `V` but is otherwise the same as `G`, it is
called the `spanningCoe` of `G`.
-/
#source spanningCoe -- spanningCoe {s : Set V} (G : SimpleGraph s) :
                    --    SimpleGraph V := G.map (Function.Embedding.subtype _)
/-!
Since `map` and `comap` along the embedding `Subtype s ↪ V` form a Galois
coinsertion, we have two very useful results relating `induce` and `spanningCoe`.

Firstly, if we start with `G : SimpleGraph ↑s` (where `s : Set V`), take its
`spanningCoe` and form the induced subgraph on `s`, then we recover `G`.
-/
example {s : Set V} {G : SimpleGraph ↑s} :
  G.spanningCoe.induce s = G := induce_spanningCoe

/-!
Secondly, if we take the `spanningCoe` of an induced subgraph we get a graph on `V`
that is a subgraph of the original graph.
-/
example {s : Set V} {G : SimpleGraph V} :
  (G.induce s).spanningCoe ≤ G := spanningCoe_induce_le ..

/-!
Moreover, recall that the `support` of a `G : SimpleGraph V` is the set of vertices
that are incident to at least one edge. The `spanningCoe` of an induced subgraph of
`G` is equal to `G` iff the support of `G` is contained in the set of vertices we are
inducing on.
-/
example {s : Set V} {G : SimpleGraph V} :
  (G.induce s).spanningCoe = G ↔ G.support ⊆ s := spanningCoe_induce_eq_self ..

/-!
We have now met three ways of describing a subgraph of `G : SimpleGraph V`: a graph
`H ≤ G` with the same vertex type `V`
([Order](https://jt496.github.io/GraphTheoryInLean/SimpleGraph/#section-order)), such
as `(G.induce s).spanningCoe`; an induced subgraph `G.induce s : SimpleGraph ↑s`,
whose vertex type is the subtype `↑s` of `V`; and a copy `Copy A G` of a graph `A`
whose vertices may have any type
([Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies)). Mathlib
has a fourth, `G.Subgraph`, in which the vertex set can vary inside `V`. We compare
all four in
[Which Notion of Subgraph?](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-which-notion-of-subgraph).
-/

/-!
# Hypercubes and Mycielskians

We now introduce the natural maps associated with hypercubes and Mycielskians.

## Embeddings of Hypercubes

There are two natural embeddings of `Q[n]` into `Q[n + 1]`, given by sending a vertex
`v` to `(v, false)` or `(v, true)`. These will be very useful when we start looking
at walks in the hypercube. We can define these in terms of the `boxProdLeft` graph
embedding.
-/
#check boxProdLeft --  G ↪g G □ H

/-- The embedding `Q[n] ↪g Q[n + 1]`, with `v ↦ (v, b)` (where `b : Bool`). -/
@[simps!]
def hypercube.embedBool (n : ℕ) (b : Bool) : Q[n] ↪g Q[n + 1] :=
  Q[n].boxProdLeft _ b

/-- The embedding `Q[n] ↪g Q[n + 1]`, with `v ↦ (v, false)`. -/
abbrev hypercube.embedFalse (n : ℕ) : Q[n] ↪g Q[n + 1] :=
  hypercube.embedBool n false

/-- The embedding `Q[n] ↪g Q[n + 1]`, with `v ↦ (v, true)`. -/
abbrev hypercube.embedTrue (n : ℕ) : Q[n] ↪g Q[n + 1] :=
  hypercube.embedBool n true

/-!
## Embeddings and Maps of Mycielskians

There is a natural embedding of a graph `G` into its Mycielskian `mμ[G]`, given
by sending a vertex `v` to the left copy of `v` in the Mycielskian.
-/
/-- The graph embedding `G ↪g mμ[G]` of a graph into its Mycielskian. -/
@[simps]
def Embedding.mycielskianLeft {V : Type*} (G : SimpleGraph V) : G ↪g mμ[G] where
  toFun := (·ₗ) -- V → Option (V ⊕ V); v ↦ some (Sum.inl v)
  inj' := Option.some_injective _ |>.comp Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-!
Any graph homomorphism `f : G →g H` induces a homomorphism `mμ[G] →g mμ[H]`. Notice
that below we use some useful shorthand for defining a function on `Option (V ⊕ V)`.
-/
#check Option.elim'
#check Sum.elim

/-- A graph homomorphism `f : G →g H` induces a homomorphism `mμ[G] →g mμ[H]`,
showing that the Mycielskian is functorial on `SimpleGraph.Hom`. -/
@[simps]
def Hom.mapMycielskian {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : mμ[G] →g mμ[H] where
  toFun := Option.elim' none <| Sum.elim (fun v => (f v)ₗ) (fun v => (f v)ᵣ)
  map_rel' := by
    intro u v h
    rcases u with _ | (_|_) <;> rcases v with _ | (_|_) <;>
      simp_all [f.map_adj]

/-- `Hom.mapMycielskian` sends the identity homomorphism on `G` to the identity on
`mμ[G]`. -/
theorem Hom.mapMycielskian_id {V : Type*} (G : SimpleGraph V) :
    (Hom.id (G := G)).mapMycielskian = Hom.id := by
  ext x; rcases x with _ | (_|_) <;> rfl

/-!
`Hom.mapMycielskian` distributes over composition: the map induced by `g.comp f` is
the composite of the maps induced by `f` and `g`. (Together with
`Hom.mapMycielskian_id` this says that the Mycielskian is a *functor* on the category
of simple graphs and homomorphisms: it acts on homomorphisms as well as on graphs,
compatibly with identities and composition.)
-/
theorem Hom.mapMycielskian_comp {V W X : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {K : SimpleGraph X} (f : G →g H) (g : H →g K) :
    (g.comp f).mapMycielskian = g.mapMycielskian.comp f.mapMycielskian := by
  ext x; rcases x with _ | (_|_) <;> rfl

/-!
The same construction turns embeddings into embeddings and isomorphisms into
isomorphisms.
-/
/-- A graph embedding `f : G ↪g H` induces an embedding `mμ[G] ↪g mμ[H]`. -/
@[simps]
def Embedding.mapMycielskian {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) : mμ[G] ↪g mμ[H] where
  toFun := f.toHom.mapMycielskian
  inj' u v h := by
    rcases u with _ | (_|_) <;> rcases v with _ | (_|_) <;> simp_all
  map_rel_iff' {u v} := by
    rcases u with _ | (_|_) <;> rcases v with _ | (_|_) <;> simp [Hom.mapMycielskian]

/-- A graph isomorphism `f : G ≃g H` induces an isomorphism `mμ[G] ≃g mμ[H]`. -/
@[simps]
def Iso.mapMycielskian {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : mμ[G] ≃g mμ[H] where
  toFun  := f.toHom.mapMycielskian
  invFun := f.symm.toHom.mapMycielskian
  left_inv x := by rcases x with _ | (_|_) <;> simp
  right_inv x := by rcases x with _ | (_|_) <;> simp
  map_rel_iff' := f.toEmbedding.mapMycielskian.map_rel_iff

/-!
# Automorphisms

An *automorphism* of a graph `G` is an isomorphism `G ≃g G` from `G` to itself. The
automorphisms of `G` form a group under composition, the *automorphism group* of `G`,
which we study in
[Algebraic Graph Theory](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#chapter-algebraic-graph-theory).
In this section we use automorphisms to define vertex-transitivity, and show that
complete graphs, cycles and hypercubes are vertex-transitive (empty graphs are left
to the exercises), while the Mycielskian of a finite nonempty graph `G` is
vertex-transitive only when `G` is a single edge.

## Vertex-Transitivity

A graph is *vertex-transitive* if its automorphism group acts transitively on the
vertices: any vertex can be sent to any other by some automorphism `G ≃g G`.

This isn't currently in Mathlib, so we introduce it here. (We use `∃` here
rather than `Nonempty`. `Nonempty T` says that the type `T` has an element, while
`∃ x : T, p x` says that some element of `T` satisfies an extra condition `p`. So
`IsContained` is `Nonempty (Copy A B)`, because the conditions on a copy are built
into the type `Copy A B`. There is no type of automorphisms sending `u` to `v`, so
here we use `∃`. The two are equivalent: `nonempty_subtype` says
`Nonempty {x // p x} ↔ ∃ x, p x`, and simp uses it to rewrite to the `∃` form.)
-/
/-- `G` is *vertex-transitive* if for every pair of vertices `u` and `v` there is an
automorphism of `G` mapping `u` to `v`. -/
abbrev IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ f : G ≃g G, f u = v

/-- Any vertex-transitive graph is regular. -/
theorem isRegular_of_isVertexTransitive {V : Type*} {G : SimpleGraph V}
    [G.LocallyFinite] (h : G.IsVertexTransitive) : ∃ d, G.IsRegularOfDegree d := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · exact ⟨0, isEmptyElim⟩
  · exact ⟨G.degree v₀, fun v => by obtain ⟨f, rfl⟩ := h v₀ v; simp⟩

/-- Isomorphisms preserve vertex-transitivity. -/
lemma Iso.isVertexTransitive {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (h : G.IsVertexTransitive) : H.IsVertexTransitive := by
  intro u v
  obtain ⟨g, hg⟩ := h (f.symm u) (f.symm v)
  exact ⟨(f.comp g).comp f.symm, by simp [hg]⟩

/-!
The complete graph is vertex-transitive, since swapping any pair of vertices gives an
automorphism of the graph. Obviously any equivalence of the underlying type gives
an automorphism: this is Mathlib's `Iso.completeGraph`.
-/
#check Iso.completeGraph -- (f : α ≃ β) : completeGraph α ≃g completeGraph β

/-- The complete graph is vertex-transitive. -/
lemma isVertexTransitive_top {V : Type*} :
    IsVertexTransitive (⊤ : SimpleGraph V) := by
  intro u v
  classical
  exact ⟨Iso.completeGraph (Equiv.swap u v), Equiv.swap_apply_left u v⟩

/-!
The empty graph is vertex-transitive too: the exercises deduce this from the complete
graph, by showing that the complement of a vertex-transitive graph is
vertex-transitive.

The cycle graph `C[n]` is vertex-transitive. To prove this we define an automorphism
of `C[n]` by rotating the vertices modulo `n`: the rotation `cycleGraphRotate d` is
the one sending the vertex `d` to `0`, i.e. `x ↦ x - d`. (Rotating in this direction
rather than `x ↦ x + d` makes the rotations match Mathlib's conventions for dihedral
groups, as we shall see in
[Automorphisms of Cycle Graphs](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-automorphisms-of-cycle-graphs).)
The definition makes sense for every `n`, with the cases `n = 0, 1` trivial since
`C[n]` is `⊥` there; only the proofs need to treat the degenerate cases separately.
-/
/-- The automorphism of the cycle graph `C[n]` given by rotating the vertices
modulo `n`, sending the vertex `d : Fin n` to `0`. -/
@[simps]
def cycleGraphRotate {n : ℕ} (d : Fin n) : C[n] ≃g C[n] where
  toFun x := x - d
  invFun x := x + d
  left_inv x := by cases n <;> grind
  right_inv x := by cases n <;> grind
  map_rel_iff' := by
    match n with
    | 0 | 1 | n + 2 => simp [cycleGraph_adj]

/-- The cycle `C[n]` is vertex-transitive for all `n`. The rotation sending
`u - v` to `0` sends `u` to `v`. (For `n = 0` there is nothing to prove since
there are no vertices.) -/
lemma isVertexTransitive_cycleGraph (n : ℕ) : C[n].IsVertexTransitive :=
  match n with
  | 0 => fun u _ => u.elim0
  | _ + 1 => fun u v => ⟨cycleGraphRotate (u - v), sub_sub_cancel u v⟩

/-!
## Vertex-Transitivity of Hypercubes

The hypercube is vertex-transitive: "translation" by a fixed vertex `t`, i.e.
componentwise `xor` with `t`, is an automorphism of `Q[n]`, and translating by
`u.xor v` sends `u` to `v`.
-/
/-- Componentwise `xor` (symmetric difference) of two hypercube vertices. -/
def HypercubeVert.xor : {n : ℕ} → HypercubeVert n → HypercubeVert n → HypercubeVert n
  | 0,     _,      _      => ()
  | _ + 1, (v, a), (w, b) => (v.xor w, a ^^ b)

/-!
Notation `v ⊕ₕ w` for the componentwise `xor` of hypercube vertices
`v w : HypercubeVert n`, i.e. addition in `(ℤ/2)ⁿ`. (We use `⊕ₕ` rather than `⊕` to
avoid clashing with the `Sum` notation `α ⊕ β`.)
-/
@[inherit_doc HypercubeVert.xor]
scoped infixl:65 " ⊕ₕ " => HypercubeVert.xor

/-- `xor`-ing twice by the same vertex is the identity, so translation is an
involution. -/
@[simp]
lemma HypercubeVert.xor_xor {n : ℕ} (v t : HypercubeVert n) : (v ⊕ₕ t) ⊕ₕ t = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨v, a⟩ := v; obtain ⟨t, s⟩ := t
    exact Prod.ext (ih v t) (by cases a <;> cases s <;> rfl)

/-!
We record this using Mathlib's `Function.Involutive`, which gives us injectivity
and the inverse equivalence for free.
-/
lemma HypercubeVert.xor_involutive {n : ℕ} (t : HypercubeVert n) :
    Function.Involutive (· ⊕ₕ t) :=
  (HypercubeVert.xor_xor · t)

/-- `xor`-ing `u` into `u ⊕ₕ v` recovers `v`. -/
@[simp]
lemma HypercubeVert.xor_xor_cancel {n : ℕ} (u v : HypercubeVert n) :
    u ⊕ₕ (u ⊕ₕ v) = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨u, a⟩ := u
    obtain ⟨v, b⟩ := v
    exact Prod.ext (ih u v) (by cases a <;> cases b <;> rfl)

/-- Translation by `t` is injective. -/
@[simp]
lemma HypercubeVert.xor_left_inj {n : ℕ} {v w t : HypercubeVert n} :
    v ⊕ₕ t = w ⊕ₕ t ↔ v = w :=
  (HypercubeVert.xor_involutive t).injective.eq_iff

/-- Translating both vertices of a potential edge by `t` preserves adjacency in
`Q[n]`. -/
lemma HypercubeVert.xor_adj {n : ℕ} (v w t : HypercubeVert n) :
    Q[n].Adj (v ⊕ₕ t) (w ⊕ₕ t) ↔ Q[n].Adj v w := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases v; cases w; cases t
    simp [ih, HypercubeVert.xor]

/-- Translation of `Q[n]` by a fixed vertex `t`, via componentwise `xor`, as a graph
automorphism. -/
def hypercubeTranslate {n : ℕ} (t : HypercubeVert n) : Q[n] ≃g Q[n] where
  toEquiv := (HypercubeVert.xor_involutive t).toPerm
  map_rel_iff' := HypercubeVert.xor_adj _ _ t

/-- The hypercube `Q[n]` is vertex-transitive. -/
lemma isVertexTransitive_hypercube (n : ℕ) : Q[n].IsVertexTransitive :=
  fun u v => ⟨hypercubeTranslate (u ⊕ₕ v), HypercubeVert.xor_xor_cancel u v⟩

/-!
We do not describe the full automorphism group of `Q[n]` here: it is the wreath
product `ℤ/2 ≀ Sₙ`, generated by the translations above together with permutations of
the coordinates. While our construction of the hypercube using the vertices
`HypercubeVert n` is very convenient for inductive proofs, to talk about the
"coordinates" of a vertex it is better to use `Fin n → Bool`. We return to this in
[The Hypercube and the Hamming Cube](https://jt496.github.io/GraphTheoryInLean/Algebraic-Graph-Theory/#section-the-hypercube-and-the-hamming-cube),
where we give a graph isomorphism `Q[n] ≃g hypercubeHamming n` between our hypercube
and the Hamming cube on `Fin n → Bool`, and then use it to identify the automorphism
group of `Q[n]` as `ℤ/2 ≀ Sₙ`.

## Vertex-Transitivity of Mycielskians

The Mycielskian of a graph is rarely vertex-transitive. In fact we can see this
easily by looking at degrees, which are equal in any vertex-transitive graph
(`isRegular_of_isVertexTransitive`). If `V` is finite and nonempty then `mμ[G]` is
vertex-transitive iff `G` is isomorphic to `K[2]`.

To help in the proof we first construct a graph isomorphism from `mμ[K[2]]` to
`C[5]`, which we already know to be vertex-transitive. We define both maps using
Mathlib's *vector notation*: `![a, b, c]` is the function `Fin 3 → α` sending `0`,
`1` and `2` to `a`, `b` and `c`. So the forward map sends the apex `none` to `0`,
`0 ₗ` and `1 ₗ` to `3` and `2`, and `0 ᵣ` and `1 ᵣ` to `1` and `4`.

[Figure: Left: $K_2$. Right: its Mycielskian drawn as a $5$-cycle. The orange numbers are the vertices of $C_5$ to which `isoMycielskianCompleteTwoCycleGraphFive` sends them](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_K2.svg)
-/
/-- A graph isomorphism from `mμ[K[2]]` to `C[5]`. -/
def isoMycielskianCompleteTwoCycleGraphFive : mμ[K[2]] ≃g C[5] where
  toFun := Option.elim' 0 (Sum.elim ![3, 2] ![1, 4])
  invFun := ![none, 0 ᵣ, 1 ₗ, 0 ₗ, 1 ᵣ]
  left_inv := by decide +revert
  right_inv := by decide +revert
  map_rel_iff' := by decide +revert

/-!
The forward direction only needs `mμ[G]` to be regular, so we isolate it as a lemma:
comparing the degrees of `u ₗ`, `u ᵣ` and `none` shows that if `V` is finite and
nonempty and `mμ[G]` is regular then `G` is a single edge.
-/
lemma nonempty_iso_completeGraph_two_of_regular_mycielskian {V : Type*}
    {G : SimpleGraph V} [Finite V] [Nonempty V] [mμ[G].LocallyFinite] {d : ℕ}
    (hd : mμ[G].IsRegularOfDegree d) : Nonempty (G ≃g K[2]) := by
  classical
  obtain ⟨v : V⟩ := ‹Nonempty V›
  cases nonempty_fintype V
  -- From `d = 2 * G.degree u` and `d = G.degree u + 1` we get `G.degree u = 1`.
  have h1 : G.IsRegularOfDegree 1 := fun u => by
    have hₗ : mμ[G].degree (u ₗ) = 2 * G.degree u := by simp
    have hᵣ : mμ[G].degree (u ᵣ) = G.degree u + 1 := by simp
    grind [hd (u ₗ), hd (u ᵣ)]
  -- Then `d = Fintype.card V` forces `Fintype.card V = 2`, as required.
  have hcard : Fintype.card V = 2 := by
    have h₀ : mμ[G].degree none = Fintype.card V := by simp
    have hᵣ : mμ[G].degree (v ᵣ) = G.degree v + 1 := by simp
    grind [hd none, hd (v ᵣ), h1 v]
  -- we now use the fact that if `G` is regular of degree `Fintype.card V - 1`
  -- then `G` is complete.
  obtain rfl : G = ⊤ :=
    G.isRegularOfDegree_card_sub_one_iff_eq_top.1 (by simpa [hcard] using h1)
  exact ⟨Iso.completeGraph (Fintype.equivFinOfCardEq hcard)⟩

/-- The Mycielskian of a graph on a finite nonempty vertex type is vertex-transitive
iff the original graph is isomorphic to `K[2]`. -/
theorem isVertexTransitive_mycielskian_iff {V : Type*} (G : SimpleGraph V) [Finite V]
    [Nonempty V] : mμ[G].IsVertexTransitive ↔ Nonempty (G ≃g K[2]) := by
  classical
  constructor
  · intro h
    cases nonempty_fintype V
    obtain ⟨d, hd⟩ := isRegular_of_isVertexTransitive h
    exact nonempty_iso_completeGraph_two_of_regular_mycielskian hd
  · intro ⟨e⟩
    exact (e.mapMycielskian.symm.comp isoMycielskianCompleteTwoCycleGraphFive.symm)
      |>.isVertexTransitive (isVertexTransitive_cycleGraph _)

/-!
# Tensor Products *

As a further example of a construction using `SimpleGraph.comap`, we define the
*tensor product* of two graphs, and then the tensor product of an indexed family of
graphs.
-/
/-- The tensor product `G ⊗g H` of graphs on `V` and `W` is the `SimpleGraph (V × W)`
where two vertices `(v₁, w₁)` and `(v₂, w₂)` are adjacent iff `G.Adj v₁ v₂` and
`H.Adj w₁ w₂`. -/
def tensorProd {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) :=
  G.comap Prod.fst ⊓ H.comap Prod.snd

/-!
We introduce the notation `G ⊗g H` for the tensor product of two graphs.
-/
@[inherit_doc]
scoped infixl:70 " ⊗g " => SimpleGraph.tensorProd

/-!
Adjacency in the tensor product is given by the adjacency relations of the two
graphs. (As for Mathlib's `boxProd_adj`, we state this as an `↔` lemma, so that it
can be used with `.1`/`.2` as well as with `rw` and `simp`.)

[Figure: Tensor product $P_3\otimes K_3$](https://jt496.github.io/GraphTheoryInLean/figures/tensorprod.svg)
-/
@[simp]
lemma tensorProd_adj {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : V × W} : (G ⊗g H).Adj x y ↔ G.Adj x.1 y.1 ∧ H.Adj x.2 y.2 := Iff.rfl

example {V W : Type*} {G H} {v₁ v₂ : V} {w₁ w₂ : W} :
    (G ⊗g H).Adj (v₁, w₁) (v₂, w₂) ↔ G.Adj v₁ v₂ ∧ H.Adj w₁ w₂ := Iff.rfl

/-!
Decidable adjacency for tensor products follows from decidable adjacency for the two
graphs.
-/
instance {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel H.Adj] : DecidableRel (G ⊗g H).Adj :=
  fun _ _ ↦ decidable_of_iff' _ tensorProd_adj

/-!
If `x.1` and `x.2` have finite neighbourhoods in `G` and `H` respectively, then so
does `x` in `G ⊗g H`, since its neighbourhood is the product `s ×ˢ t` of the two
neighbourhoods. (We state the instance for `x : V × W` rather than for a pair
`(v, w)`, since otherwise it would not fire on a general `x : V × W`.)
-/
/-- If `G` and `H` have finite neighbourhoods at `x.fst` and `x.snd` respectively,
then their tensor product has a finite neighbourhood at `x`. -/
instance {V W : Type*} {x : V × W} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype (G.neighborSet x.fst)] [Fintype (H.neighborSet x.snd)] :
    Fintype ((G ⊗g H).neighborSet x) :=
  Fintype.ofFinset (G.neighborFinset x.fst ×ˢ H.neighborFinset x.snd) (by simp)

/-- The degree of a vertex in the tensor product is the product of the degrees of its
components. -/
lemma degree_tensorProd {V W : Type*} {x : V × W} {G : SimpleGraph V}
    {H : SimpleGraph W} [Fintype (G.neighborSet x.fst)]
    [Fintype (H.neighborSet x.snd)] [Fintype ((G ⊗g H).neighborSet x)] :
    (G ⊗g H).degree x = G.degree x.fst * H.degree x.snd := by
  simp_rw [← card_neighborFinset_eq_degree, ← Finset.card_product]
  congr
  ext ⟨x, y⟩
  simp

/-!
## Maps of Tensor Products

The two projections `Prod.fst` and `Prod.snd` are graph homomorphisms out of
`G ⊗g H`. Conversely, a pair of homomorphisms from a common graph `K` into `G` and
`H` combines into a single homomorphism `K →g G ⊗g H`. So homomorphisms into
`G ⊗g H` are exactly pairs of homomorphisms into `G` and `H`. (In the language of
category theory: the tensor product is the *product* in the category of simple graphs
and homomorphisms.)
-/
/-- The first projection is a graph homomorphism `G ⊗g H →g G`. -/
def tensorProd.fstHom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} :
    G ⊗g H →g G where
  toFun := Prod.fst
  map_rel' h := h.1

/-- The second projection is a graph homomorphism `G ⊗g H →g H`. -/
def tensorProd.sndHom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} :
    G ⊗g H →g H where
  toFun := Prod.snd
  map_rel' h := h.2

/-- Pairing two homomorphisms `f : K →g G` and `g : K →g H` gives a homomorphism into
the tensor product. This is the universal property of the product. -/
def tensorProd.prod {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph X} (f : K →g G) (g : K →g H) : K →g G ⊗g H where
  toFun x := (f x, g x)
  map_rel' h := ⟨f.map_adj h, g.map_adj h⟩

/-!
Composing a colouring of `G` with the projection `tensorProd.fstHom` gives a
colouring of `G ⊗g H`, and similarly for `H`. So the chromatic number of `G ⊗g H` is
at most the minimum of the chromatic numbers of `G` and `H`.
-/
example {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (h : G.Colorable n) : (G ⊗g H).Colorable n :=
  Colorable.of_hom tensorProd.fstHom h

/-!
## Indexed Tensor Products

The tensor product generalizes, using the *indexed infimum* `⨅`, to the product of an
arbitrary indexed family of graphs.
-/
/-- The indexed tensor product of a family of graphs, denoted `⨂g i, G i`. -/
def piTensorProd {ι : Type*} {V : ι → Type*} (G : (i : ι) → SimpleGraph (V i)) :
    SimpleGraph ((i : ι) → V i) := ⨅ i, (G i).comap (fun f ↦ f i)

@[inherit_doc piTensorProd]
scoped notation3 "⨂g "(...)", "r:67:(scoped G => SimpleGraph.piTensorProd G) => r

/-!
Adjacency in the indexed tensor product is given by adjacency in each component graph
*and* the vertices being distinct. The distinctness condition is inherited from
`SimpleGraph.iInf_adj`. When `ι` is nonempty it follows from adjacency in any one
component, so it only matters when `ι` is empty. Then `(i : ι) → V i` has a single
element, and without the distinctness condition this vertex would be adjacent to
itself.
-/
@[simp]
lemma piTensorProd_adj {ι : Type*} {V : ι → Type*} {G : (i : ι) → SimpleGraph (V i)}
    {f g : (i : ι) → V i} :
    (⨂g i, G i).Adj f g ↔ (∀ i, (G i).Adj (f i) (g i)) ∧ f ≠ g :=
  iInf_adj

/-!
So when `ι` is nonempty, adjacency in the indexed tensor product is just adjacency in
every component. (We give this higher simp priority than `piTensorProd_adj`, so that
it fires first when `ι` is nonempty.)
-/
@[simp high]
lemma piTensorProd_adj_of_nonempty {ι : Type*} [Nonempty ι] {V : ι → Type*}
    {G : (i : ι) → SimpleGraph (V i)} {f g : (i : ι) → V i} :
    (⨂g i, G i).Adj f g ↔ ∀ i, (G i).Adj (f i) (g i) := by
  rw [piTensorProd_adj]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact fun e => (h i).ne (congrFun e i)

/-!
We can only expect to decide adjacency in the indexed tensor product by checking
every factor when the index type is finite: you can't check infinitely many
conditions! The tensor product of a finite family of graphs has decidable
adjacency if each graph in the family has decidable adjacency and each vertex type
has decidable equality. (Decidable equality is needed to decide the distinctness
condition `f ≠ g`.)
-/
instance {ι : Type*} {V : ι → Type*} [Fintype ι] [∀ i, DecidableEq (V i)]
    (G : (i : ι) → SimpleGraph (V i)) [∀ i, DecidableRel (G i).Adj] :
    DecidableRel (⨂g i, G i).Adj :=
  fun _ _ ↦ decidable_of_iff' _ piTensorProd_adj

/-!
If each `G i` has a finite neighbourhood at `f i` then the tensor product has a
finite neighbourhood at `f`, provided the index type is finite, nonempty and has
decidable equality.
-/
instance {ι : Type*} {V : ι → Type*} {G : (i : ι) → SimpleGraph (V i)}
    {f : (i : ι) → V i} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [∀ i, Fintype ((G i).neighborSet (f i))] :
    Fintype ((⨂g i, G i).neighborSet f) :=
  Fintype.ofFinset (Fintype.piFinset fun i ↦ (G i).neighborFinset (f i)) fun y ↦ by
    simp

/-!
The analogues for the indexed tensor product of the maps in
[Maps of Tensor Products](https://jt496.github.io/GraphTheoryInLean/Maps/#section-maps-of-tensor-products)
are in the exercises
([Exercises](https://jt496.github.io/GraphTheoryInLean/Maps/#section-exercises-maps)).

# Claw-Free Graphs *

We say that `H` contains `G` as an *induced subgraph* (up to isomorphism) if there
is an induced subgraph of `H` isomorphic to `G`, i.e. there is an embedding
`G ↪g H`. This is written `G ⊴ H`.
-/
#source IsIndContained -- def IsIndContained (G : SimpleGraph V)
                       --       (H : SimpleGraph W) : Prop := Nonempty (G ↪g H)
/-!
There isn't currently a standard name for the property of not containing an induced
copy of a graph in Mathlib, so we introduce one here (following the pattern of
`Free`).
-/
/-- `A.IndFree B` means that `B` does not contain an induced copy of `A`. -/
abbrev IndFree {V W : Type*} (A : SimpleGraph V) (B : SimpleGraph W) := ¬A ⊴ B
/-!
The *claw* is the complete bipartite graph `K[1, 3]`.
-/
/-- A graph is *claw-free* if it does not contain an induced copy of `K[1, 3]`. -/
abbrev ClawFree {V : Type*} (G : SimpleGraph V) : Prop := K[1, 3].IndFree G

/-!
Note that claw-free refers to *induced* copies of the claw. A copy of the claw that
need not be induced is just a vertex with three distinct neighbours, so being
claw-free in that sense would simply mean that every vertex has at most two
neighbours. The two notions really are different: `K[4]` is claw-free, since any four
of its vertices induce a copy of `K[4]`, yet `K[1, 3] ⊑ K[4]`, since every vertex of
`K[4]` has three neighbours (see the exercises).
-/
/-- Line graphs are always claw-free. -/
theorem clawFree_lineGraph {V : Type*} (G : SimpleGraph V) : L[G].ClawFree := by
  classical
  -- Suppose not: then we have an embedding `f` of `K[1, 3]` in `L[G]`.
  rintro ⟨f⟩
  -- The centre of the claw is adjacent to each leaf, so its edge `f (.inl 0)` shares
  -- a vertex `w i` with each leaf edge `f (.inr i)`.
  have key : ∀ i, ∃ v, v ∈ (f (.inl 0) : Sym2 V) ∧ v ∈ (f (.inr i) : Sym2 V) := by
    intro i
    have hadj : K[1, 3].Adj (.inl 0) (.inr i) := by simp
    rw [← f.map_adj_iff, lineGraph_adj_iff_exists] at hadj
    simpa using hadj
  -- The `choose` tactic turns `key` into a function `w : Fin 3 → V` together with
  -- `hwc : ∀ i, w i ∈ f (.inl 0)` and `hwl : ∀ i, w i ∈ f (.inr i)`.
  -- This uses the axiom of choice.
  choose w hwc hwl using key
  -- The centre edge is `s(a, b)` with `a ≠ b`.
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 (hwc 0)
  let a := w 0
  have hne : a ≠ b := by
    have hmem : (f (.inl 0) : Sym2 V) ∈ G.edgeSet := (f (.inl 0)).2
    rw [hb, mem_edgeSet] at hmem
    exact hmem.ne
  -- Each leaf's shared vertex is one of the two endpoints `a` or `b`.
  have hsides : ∀ i, w i = a ∨ w i = b := by grind
  -- Three leaves, two endpoints, so two leaves `i ≠ j` must share the same endpoint!
  -- We do this by the pigeonhole principle, applied to the map `Fin 3 → Prop`
  -- sending `i` to the proposition `w i = a`. This gives `i ≠ j` with `w i = a` and
  -- `w j = a` taking the same truth value and hence `w i = w j`.
  -- (Since either both are `a` or both are `≠ a` and hence equal `b`.)
  obtain ⟨i, j, hij, hsame⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (w · = a) (by decide)
  have hwij : w i = w j := by grind
  -- But then the two leaf edges share `w i`, hence are adjacent in the line graph,
  -- contradicting that leaves of the claw are non-adjacent.
  have hfne : f (.inr i) ≠ f (.inr j) := fun h => hij (by simpa using f.injective h)
  have hadj : L[G].Adj (f (.inr i)) (f (.inr j)) :=
    lineGraph_adj_iff_exists.2 ⟨hfne, w j, hwij ▸ hwl i, hwl j⟩
  simp [f.map_adj_iff] at hadj

/-!
## Triangles in Line Graphs

Our next goal is to show that the line graph of a graph `G` contains a copy of `K[3]`
iff `G` contains either a copy of `K[3]` or a copy of the claw `K[1, 3]`.

First, two simple helper lemmas, which build the required copies directly from their
vertices.
-/
/-- If `G` contains three mutually adjacent vertices then it contains a copy of the
triangle `K[3]`. -/
lemma top_three_isContained {V : Type*} {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : K[3] ⊑ G := by
  -- Map the vertices `0, 1, 2` of `K[3]` to `a, b, c` using vector notation `![ ]`.
  -- Distinct vertices of `K[3]` are adjacent, and go to adjacent vertices of `G`.
  -- `fin_cases i` splits the goal into one case for each value of `i : Fin 3`.
  let f : K[3] →g G := ⟨![a, b, c], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm, hac.symm, hbc.symm]⟩
  -- A homomorphism from a complete graph is injective, so `f` gives a copy.
  exact ⟨f.toCopy f.injective_of_top_hom⟩

/-- A vertex `a` with three distinct neighbours `b, c, d` gives a copy of the claw
`K[1, 3]`. -/
lemma claw_isContained {V : Type*} {G : SimpleGraph V} {a b c d : V} (hb : G.Adj a b)
    (hc : G.Adj a c) (hd : G.Adj a d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    K[1, 3] ⊑ G := by
  -- Map the centre of the claw `K[1, 3]` to `a` and the three leaves to `b, c, d`.
  -- We use `Sum.elim` to map the two parts of the sum type, and the
  -- vector notation `![ ]`, to map `Fin 3` as `0 ↦ b, 1 ↦ c, 2 ↦ d`.
  let φ : Fin 1 ⊕ Fin 3 → V := Sum.elim (fun _ => a) ![b, c, d]
  -- `φ` preserves adjacency: every edge of the claw maps to an edge of `G`.
  have hom : ∀ {x y : Fin 1 ⊕ Fin 3}, K[1, 3].Adj x y → G.Adj (φ x) (φ y) := by
    rintro (i | i) (j | j) h <;>
      fin_cases i <;> fin_cases j <;> -- 16 cases
        simp_all [φ, Adj.symm]
  -- `φ` is injective, since `a, b, c, d` are pairwise distinct.
  have inj : Function.Injective φ := by
    rintro (i | i) (j | j) h <;>
      fin_cases i <;> fin_cases j <;> simp_all [φ]
  -- Package the homomorphism `⟨φ, hom⟩` together with injectivity into a `Copy`.
  exact ⟨⟨φ, hom⟩, inj⟩

/-!
In a locally finite graph, we can characterize the existence of a copy of the claw in
`G` in terms of the existence of a vertex of degree at least 3.
-/
/-- A graph `G` contains a copy of the claw `K[1, 3]` iff it has a vertex of degree
at least 3. -/
theorem claw_isContained_iff {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] :
    K[1, 3] ⊑ G ↔ ∃ v, 3 ≤ G.degree v := by
  rw [exists_three_le_degree_iff]
  constructor
  · intro ⟨f⟩
    refine ⟨f (.inl 0), f (.inr 0), f (.inr 1), f (.inr 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
      <;> first
        | exact f.toHom.map_adj (by decide)
        | exact f.injective.ne (by decide)
  · rintro ⟨_, _, _, _, hb, hc, hd, hbc, hbd, hcd⟩
    exact claw_isContained hb hc hd hbc hbd hcd

/-!
Next we look at the line graphs of `K[3]` and `K[1, 3]` themselves: both are
isomorphic to `K[3]`.

[Figure: Left: $K_3$ and its line graph. Right: the claw $K_{1,3}$ and its line graph.](https://jt496.github.io/GraphTheoryInLean/figures/lineGraphTriangleClaw.svg)

In defining the two isomorphisms we make heavy use of `decide`. Indeed it is in
situations like this that we see the value of making things computable. We really
don't want to perform tedious small case analysis by hand, so we should always aim to
use `decide` or similar automation (such as `fin_cases`) where possible.
-/
/-- The line graph of `K[3]` is isomorphic to a triangle `K[3]`. -/
def lineGraphCompleteGraphThreeIso : L[K[3]] ≃g K[3] where
  toFun e := if (e : Sym2 (Fin 3)) = s(0, 1) then 0
    else if (e : Sym2 (Fin 3)) = s(0, 2) then 1 else 2
  invFun i := if i = 0 then ⟨s(0, 1), by decide⟩ else
              if i = 1 then ⟨s(0, 2), by decide⟩ else ⟨s(1, 2), by decide⟩
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-- The line graph of the claw graph `K[1, 3]` is isomorphic to a triangle `K[3]`. -/
def lineGraphClawIso : L[K[1, 3]] ≃g K[3] where
  toFun e := if (e : Sym2 (Fin 1 ⊕ Fin 3)) = s(.inl 0, .inr 0) then 0
        else if (e : Sym2 (Fin 1 ⊕ Fin 3)) = s(.inl 0, .inr 1) then 1 else 2
  invFun i := if i = 0 then ⟨s(.inl 0, .inr 0), by decide⟩ else
    if i = 1 then ⟨s(.inl 0, .inr 1), by decide⟩ else ⟨s(.inl 0, .inr 2), by decide⟩
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-!
Since containment passes to line graphs (`IsContained.lineGraph`), a copy of `K[3]`
in `G` gives a copy of `L[K[3]]`, and hence of `K[3]`, in the line graph of `G`.
Likewise a copy of the claw in `G` gives a copy of `L[K[1, 3]]`, which is again a
triangle.
-/
/-- If a graph `G` contains a triangle, then its line graph contains a triangle. -/
lemma isContained_lineGraph_of_triangle {V : Type*} {G : SimpleGraph V}
    (h : K[3] ⊑ G) : K[3] ⊑ L[G] :=
  lineGraphCompleteGraphThreeIso.isContained'.trans h.lineGraph

/-- If a graph `G` contains a claw, then its line graph contains a triangle. -/
lemma isContained_lineGraph_of_claw {V : Type*} {G : SimpleGraph V}
    (h : K[1, 3] ⊑ G) : K[3] ⊑ L[G] :=
  lineGraphClawIso.isContained'.trans h.lineGraph

/-!
Conversely, a triangle in the line graph comes from either a triangle or a copy of
the claw in `G`: three pairwise distinct, pairwise intersecting edges either share a
common vertex (giving a copy of the claw) or form a triangle.
-/
/-- If the line graph of a graph `G` contains a triangle, then `G` contains a
triangle or a copy of the claw. -/
lemma top_three_or_claw_isContained_of_isContained_lineGraph {V : Type*}
    {G : SimpleGraph V} (h : K[3] ⊑ L[G]) : K[3] ⊑ G ∨ K[1, 3] ⊑ G := by
  obtain ⟨f⟩ := h
  -- the copy `f` of `K[3]` in the line graph maps pairs of distinct vertices
  -- of `K[3]` to pairs of intersecting edges in `G`.
  have meet : ∀ i j : Fin 3, i ≠ j →
      f i ≠ f j ∧ ∃ v, v ∈ (f i : Sym2 V) ∧ v ∈ (f j : Sym2 V) := by
    intro i j hij
    have hadj : L[G].Adj (f i) (f j) := f.topEmbedding.map_adj_iff.2 hij
    rwa [lineGraph_adj_iff_exists] at hadj
  -- get the three meeting points of the three pairs of edges in `G` corresponding
  -- to the three pairs of vertices of `K[3]` in the line graph.
  obtain ⟨h01, x, hx0, hx1⟩ := meet 0 1 (by decide)
  obtain ⟨h12, y, hy1, hy2⟩ := meet 1 2 (by decide)
  obtain ⟨h02, z, hz0, hz2⟩ := meet 0 2 (by decide)
  by_cases hxy : x = y
  · -- The shared vertex `x = y` lies on all three edges: a copy of the claw centred
    -- at `x`.
    obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hx0
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 hx1
    obtain ⟨c, hc⟩ := Sym2.mem_iff_exists.1 (hxy.symm ▸ hy2)
    -- `(f i).prop : ↑(f i) ∈ G.edgeSet`, so rewriting with `ha : ↑(f 0) = s(x, a)`
    -- gives `s(x, a) ∈ G.edgeSet`, which is defeq to `G.Adj x a` (similarly for `hb`
    -- and `hc`).
    exact Or.inr <| claw_isContained (ha ▸ (f 0).prop) (hb ▸ (f 1).prop)
                      (hc ▸ (f 2).prop) (by grind) (by grind) (by grind)
  · -- Otherwise the three meeting points `x, y, z` are distinct: a triangle.
    have hf1 : (f 1 : Sym2 V) = s(x, y) := (Sym2.mem_and_mem_iff hxy).1 ⟨hx1, hy1⟩
    obtain ⟨hzx, hzy⟩ : z ≠ x ∧ z ≠ y := by grind [Sym2.mem_and_mem_iff]
    have : f 0 = s(x, z) := (Sym2.mem_and_mem_iff hzx.symm).1 ⟨hx0, hz0⟩
    have : f 2 = s(y, z) := (Sym2.mem_and_mem_iff hzy.symm).1 ⟨hy2, hz2⟩
    obtain ⟨axy, axz, ayz⟩ : G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
      grind [mem_edgeSet]
    exact Or.inl <| top_three_isContained axy axz ayz

/-!
Putting everything together we have a complete characterization.
-/
/-- The line graph of `G` contains a triangle iff `G` contains a triangle or a copy
of the claw. -/
theorem top_three_isContained_lineGraph_iff {V : Type*}
    {G : SimpleGraph V} : K[3] ⊑ L[G] ↔ K[3] ⊑ G ∨ K[1, 3] ⊑ G :=
  ⟨top_three_or_claw_isContained_of_isContained_lineGraph,
    fun h => h.elim isContained_lineGraph_of_triangle isContained_lineGraph_of_claw⟩


end SimpleGraph
