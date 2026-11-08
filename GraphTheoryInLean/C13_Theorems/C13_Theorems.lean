/-
Copyright (c) 2026 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import GraphTheoryInLean.Common
import GraphTheoryInLean.C12_Algebraic_Graph_Theory.C12_Algebraic_Graph_Theory
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Triangle.Counting
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Extremal.RuzsaSzemeredi
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Order.KonigLemma
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
namespace SimpleGraph
/-!
Mathlib formalizes quite a few classical theorems of graph theory. In this final
chapter we survey some of them, building on earlier chapters: we state each result,
explain how its statement is phrased in Lean, and (when applicable) apply it to our
running examples. Where a natural strengthening or application is missing from
Mathlib we prove it ourselves.

We begin with matchings: Hall's marriage theorem
(`exists_isMatching_of_forall_ncard_le`) and its deficiency version
(`exists_isMatching_of_forall_ncard_le_add`), from which we deduce Kőnig's theorem
(`IsBipartite.matchingNum_eq_vertexCoverNum`), and finally Tutte's theorem (`tutte`).
We then turn to extremal graph theory: Turán's theorem
(`isTuranMaximal_iff_nonempty_iso_turanGraph`, with Mantel's theorem as a special
case), Füredi's stability theorem (`CliqueFree.exists_colorable_deleteEdges`), the
Andrásfai–Erdős–Sós theorem (`colorable_of_cliqueFree_lt_minDegree`) and extremal
numbers (`extremalNumber`), together with their asymptotic behaviour: the Turán
density (`turanDensity`) and the minimum degree Erdős–Stone theorem
(`eventually_completeEquipartiteGraph_isContained_of_minDegree`).

The last three sections are more advanced, and they are independent of each other:
each builds only on the first two sections, so they can be read in any order. The
first proves Zykov's theorem on the number of cliques
(`CliqueFree.card_cliqueFinset_le`) together with its case of equality
(`CliqueFree.card_cliqueFinset_eq_iff_nonempty_iso_turanGraph`). It is a complete
proof rather than a survey, and by far the longest section of the chapter. The second
covers Szemerédi's regularity lemma (`szemeredi_regularity`) and the triangle removal
lemma (`triangle_removal`), applied to Roth's theorem on arithmetic progressions
(`roth_3ap_theorem_nat`) and the Ruzsa–Szemerédi theorem
(`ruzsaSzemerediNumberNat_isLittleO`). The third looks at two results about infinite
graphs, Kőnig's lemma (`exists_seq_covby_of_forall_covby_finite`), from which we
deduce its graph form (`Connected.pathNat_isContained`), and the existence of ends
(`nonempty_ends_of_infinite`).

Many famous theorems are not (yet) in Mathlib. These include Ramsey's theorem for
graphs, the Kővári–Sós–Turán theorem, Kirchhoff's matrix-tree theorem
[Kirchhoff 1847](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-kirchhoff-1847),
Cayley's formula
[Cayley 1889](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-cayley-1889),
Euler's circuit theorem, Euler's formula
[Euler 1758](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-euler-1758)
and planarity, Menger's theorem, Brooks' theorem, Vizing's theorem, Berge's theorem
[Berge 1957](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-berge-1957),
Kőnig's theorem on bipartite matchings and the theorems of Dirac and Ore. Some of
these are proved in this guide:

* the simplest case `R(3, 3) = 6` of Ramsey's theorem
  (`not_cliqueFree_three_and_indepSetFree_three`)
* Euler's theorem on Eulerian trails (`exists_isEulerian_iff`)
* the theorems of Dirac (`isHamiltonian_of_card_le_two_mul_minDegree`) and Ore
  (`IsOreGraph.isHamiltonian`)
* Brooks' theorem (`brooks`)
* [Kőnig's theorem](#section-k-nig-s-theorem)
  (`IsBipartite.matchingNum_eq_vertexCoverNum`)

Whole areas of graph theory are also missing. The biggest gap is probabilistic graph
theory: Mathlib defines the binomial random graph `G(V, p)` (`binomialRandom`), in
which each pair of vertices is joined independently with probability `p`, but proves
almost nothing about it, not even that a given pair is an edge with probability `p`.
So the classical applications of the probabilistic method to graphs are missing too,
including Erdős's lower bound for Ramsey numbers and his theorem on graphs of large
girth and large chromatic number
[Erdős 1959](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-erdos-1959).

# Matchings

Recall that a matching in `G` (`Subgraph.IsMatching`) is a subgraph `M` in which
every vertex of `M` has exactly one neighbour in `M`. It need not be spanning: its
vertices are the matched vertices. A perfect matching is a spanning matching, so
every vertex of `G` has exactly one `M`-neighbour.
-/
variable {V : Type*} {G : SimpleGraph V}
open Finset

example (M : G.Subgraph) : M.IsPerfectMatching ↔ ∀ v, ∃! w, M.Adj v w :=
  Subgraph.isPerfectMatching_iff

/-!
The vertices of a perfect matching are paired up, so a finite graph with a perfect
matching has an even number of vertices.
-/
#check Subgraph.IsPerfectMatching.even_card

/-!
For example, the Mycielskian `mμ(G)` of a finite graph has `2 * |V| + 1` vertices, an
odd number, so it never has a perfect matching.
-/
example [Finite V] (M : mμ(G).Subgraph) : ¬ M.IsPerfectMatching := fun hM => by
  have := Fintype.ofFinite V
  simpa [Nat.even_add_one] using hM.even_card

/-!
The classical existence results for perfect matchings are Hall's marriage theorem
(for bipartite graphs) and Tutte's theorem (for general graphs).

## Hall's Marriage Theorem

Let `G` be bipartite with parts `p₁` and `p₂` (`IsBipartiteWith`). *Hall's condition*
says that every finite set `s ⊆ p₁` has at least `|s|` neighbours. *Hall's theorem*
[Hall 1935](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-hall-1935)
says that this condition implies that `G` has a matching whose vertices include all
of `p₁`. (The converse is easy: the partners of the vertices in `s` are distinct
neighbours of `s`.)

[Figure: A bipartite graph with a subset $s$ and its open neighbourhood $N(s)$](https://jt496.github.io/GraphTheoryInLean/figures/hall.svg)
-/
#check exists_isMatching_of_forall_ncard_le

/-!
Notice that `V` need not be finite: Mathlib only assumes that `G` is locally finite,
and we will see that even this is more than the proof needs. Hall's condition is
stated with `Set.ncard`, which is `0` on infinite sets, so it holds trivially for
infinite `s` and only finite sets need to be checked.
-/
#check Set.Infinite.ncard -- s.Infinite → s.ncard = 0

example {s : Set V} (hs : s.Infinite) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  simp [hs.ncard]

/-!
For a perfect matching, Mathlib asks for Hall's condition for every set `s` of
vertices, which may contain vertices from both sides.
-/
#check exists_isPerfectMatching_of_forall_ncard_le

/-!
Both theorems come from the statement about *systems of distinct representatives*: a
family of finite sets `t : ι → Finset α` has an injective choice function iff every
union of `k` of the sets has at least `k` elements. Mathlib states it for any index
type `ι`. For infinite `ι` it follows from the finite case by a compactness argument:
each finite set of indices has at least one injective choice and only finitely many,
and `nonempty_sections_of_finite_inverse_system` makes the choices agree.
-/
#check Finset.all_card_le_biUnion_card_iff_exists_injective

/-!
Mathlib applies it to the finsets `G.neighborFinset x` with `x ∈ p₁`, and it is to
form these that it assumes `[G.LocallyFinite]`. For a perfect matching it applies it
to all of `V`, which is why the condition is stated for all sets of vertices. This
gives injections `p₁ → p₂` and `p₂ → p₁` along edges. If `V` is finite then
`|p₁| = |p₂|`, and either one is already a perfect matching. In general Mathlib
combines them using a relational form of the Schröder–Bernstein theorem
(`Function.Embedding.schroeder_bernstein_of_rel`), which yields a bijection `p₁ → p₂`
along edges.
-/
#check exists_bijective_of_forall_ncard_le

/-!
Local finiteness cannot be dropped from the classical theorem. An example is a
*subdivided star*: a star with each edge subdivided by a new vertex. Its vertices are
a centre and two copies of an index type `ι`, so we reuse the vertex type
`Option (ι ⊕ ι)` of the Mycielskian and its notation: the centre `none` is adjacent
to every `iʳ`, and each `iˡ` is adjacent only to `iʳ`.
-/
/-- The *subdivided star* on `ι`: the centre `none` is adjacent to every `iʳ`, and
each `iˡ` is adjacent only to `iʳ`. -/
@[simps]
def subdividedStar (ι : Type*) : SimpleGraph (Option (ι ⊕ ι)) where
  Adj x y := match x, y with
    | none, _ʳ | _ʳ, none => True
    | iˡ, jʳ | jʳ, iˡ => i = j
    | _, _ => False
  symm := ⟨by rintro (_ | _ | _) (_ | _ | _) h <;> simp_all [eq_comm]⟩
  loopless := ⟨by rintro (_ | _ | _) <;> simp⟩

/-!
In `subdividedStar ℕ`, every finite set of the vertices `none, 0ˡ, 1ˡ, …` has at
least as many neighbours as elements, but no matching covers them all: whichever `jʳ`
is matched to `none`, the vertex `jˡ` is left unmatched, since `jʳ` is its only
neighbour. In particular, a subdivided star has no perfect matching.

[Figure: The subdivided star `subdividedStar ℕ`. A matching (red) covering `none` ($\ast$) leaves a vertex (orange) unmatched](https://jt496.github.io/GraphTheoryInLean/figures/hall_infinite.svg)
-/
/-- A subdivided star has no perfect matching. -/
lemma not_exists_isPerfectMatching_subdividedStar {ι : Type*} :
    ¬ ∃ M : (subdividedStar ι).Subgraph, M.IsPerfectMatching := by
  rintro ⟨M, hM, hspan⟩
  -- `none` is matched to a right vertex `jʳ`
  obtain ⟨w, hw, -⟩ := hM (hspan none)
  obtain _ | j | j := w
  · simpa using M.adj_sub hw
  · simpa using M.adj_sub hw
  -- `jˡ` is matched to `jʳ` as well
  obtain ⟨u, hu, -⟩ := hM (hspan jˡ)
  obtain _ | k | k := u
  · simpa using M.adj_sub hu
  · simpa using M.adj_sub hu
  obtain rfl : j = k := by simpa using M.adj_sub hu
  simpa using hM.eq_of_adj_right hw hu

/-!
In Lean, though, this graph fails Hall's condition for the set `{none}`: `none` has
infinitely many neighbours, so the `Set.ncard` of its neighbourhood is `0`.
-/
example : ¬ ({none} : Set (Option (ℕ ⊕ ℕ))).ncard ≤
    (⋃ x ∈ ({none} : Set _), (subdividedStar ℕ).neighborSet x).ncard := by
  -- the neighbours of `none` are the right vertices `iʳ`
  have h : ((subdividedStar ℕ).neighborSet none).Infinite :=
    Set.infinite_of_injective_forall_mem mycielskian.right_injective (by simp)
  simp [h.ncard]

/-!
So Lean's statement of Hall's condition already forces every vertex of `p₁` to have
finite degree. `exists_isMatching_of_forall_ncard_le` assumes `[G.LocallyFinite]`,
which asks the same of `p₂`, but its proof does not need this: it picks partners for
the vertices of `p₁` from their neighbourhoods and never looks at the neighbourhood
of a vertex in `p₂`. Mathlib's relational form of the theorem on systems of distinct
representatives asks for exactly this one-sided finiteness: each `a : α` must be
related to finitely many elements of `β`, and nothing is assumed about `β`.
-/
#check Fintype.all_card_le_rel_image_card_iff_exists_injective

/-!
## Kőnig's Theorem

In `matchingNum_le_vertexCoverNum` we proved weak duality `ν G ≤ τ G`: a vertex cover
needs to hit every edge of a matching. *Kőnig's theorem*
[Kőnig 1931](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-konig-1931)
says that for bipartite graphs this is an equality. It is not in Mathlib, but we can
deduce it from a *deficiency version* of Hall's theorem.

Suppose that every finite `s ⊆ p₁` has at least `|s| - d` neighbours. We show that we
can then match all but at most `d` vertices of `p₁`. Add `d` new vertices adjacent to
every vertex of `p₁`. Hall's condition now holds, so the systems of distinct
representatives theorem gives an injective choice of neighbours `g`, with values in
`V ⊕ Fin d`. At most `d` vertices of `p₁` are sent to new vertices, and the others
are sent injectively to neighbours in `G`, which gives a matching by
`exists_isMatching_of_injective`. We state this last step separately: it is the only
one that uses the bipartition.

Mathlib's proofs of Hall's theorem build the matching from the chosen neighbours by
hand, but the same construction is available as a lemma: a bijection `f : s ≃ t`
between disjoint sets, with each `v` adjacent to `f v`, gives a matching with vertex
set `s ∪ t`.
-/
#check Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv

/-!
In a bipartite graph, an injective choice of neighbours `f` for the vertices of
`s ⊆ p₁` is such a bijection onto its range, since the range lies in `p₂`, which is
disjoint from `s`. So the edges `x — f x` form a matching covering `s`.
-/
lemma exists_isMatching_of_injective {p₁ p₂ s : Set V} (h₁ : G.IsBipartiteWith p₁ p₂)
    (hs : s ⊆ p₁) (f : s → V) (hf : Function.Injective f)
    (hadj : ∀ x : s, G.Adj x (f x)) :
    ∃ M : Subgraph G, s ⊆ M.verts ∧ M.IsMatching := by
  have hd : Disjoint s (Set.range f) := h₁.disjoint.mono hs
    (Set.range_subset_iff.mpr fun x =>
      h₁.mem_of_mem_adj (hs x.2) (hadj x))
  obtain ⟨M, hverts, hM⟩ :=
    Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
      hd (Equiv.ofInjective f hf) hadj
  exact ⟨M, hverts ▸ Set.subset_union_left, hM⟩

/-!
We count the unmatched vertices with `Set.encard`, not `Set.ncard`. Since the latter
is `0` on infinite sets, `(p₁ \ M.verts).ncard ≤ d` would also hold if infinitely
many vertices of `p₁` were unmatched.
-/
/-- An injective choice, for each vertex of `p₁`, of either a neighbour or one of `d`
new vertices gives a matching that covers all but at most `d` vertices of `p₁`. -/
lemma exists_isMatching_of_injective_sum {p₁ p₂ : Set V} {d : ℕ}
    (h₁ : G.IsBipartiteWith p₁ p₂) (g : p₁ → V ⊕ Fin d) (hg : Function.Injective g)
    (hadj : ∀ x y, g x = .inl y → G.Adj x y) :
    ∃ M : Subgraph G, M.IsMatching ∧ (p₁ \ M.verts).encard ≤ d := by
  -- the vertices `X` of `p₁` that chose an old vertex are matched in `G`
  let X : Set V := {x | ∃ hx : x ∈ p₁, (g ⟨x, hx⟩).isLeft}
  have hX : X ⊆ p₁ := fun x hx => hx.1
  let f : X → V := fun x => (g ⟨x, x.2.1⟩).getLeft x.2.2
  have hgf (x : X) : g ⟨x, x.2.1⟩ = .inl (f x) := (Sum.inl_getLeft _ _).symm
  have hf : Function.Injective f := fun x y hxy => by
    have hgxy : g ⟨x, x.2.1⟩ = g ⟨y, y.2.1⟩ := by rw [hgf, hgf, hxy]
    simpa [Subtype.ext_iff] using hg hgxy
  obtain ⟨M, hXM, hM⟩ :=
    exists_isMatching_of_injective h₁ hX f hf fun x => hadj _ _ (hgf x)
  refine ⟨M, hM, (Set.encard_le_encard (Set.sdiff_subset_sdiff_right hXM)).trans ?_⟩
  -- the other vertices of `p₁` chose distinct new vertices
  have hp (x : ↑(p₁ \ X)) : (x : V) ∈ p₁ := x.2.1
  have hr (x : ↑(p₁ \ X)) : (g ⟨x, hp x⟩).isRight := by
    simpa [X, hp x] using x.2.2
  let φ : ↑(p₁ \ X) → Fin d := fun x => (g ⟨x, hp x⟩).getRight (hr x)
  have hgφ (x : ↑(p₁ \ X)) : g ⟨x, hp x⟩ = .inr (φ x) := (Sum.inr_getRight _ _).symm
  have hφ : Function.Injective φ := fun x y hxy => by
    have hgxy : g ⟨x, hp x⟩ = g ⟨y, hp y⟩ := by rw [hgφ, hgφ, hxy]
    simpa [Subtype.ext_iff] using hg hgxy
  simpa using ENat.card_le_card_of_injective hφ

/-!
What remains is to check Hall's condition after adding the new vertices. For `d > 0`
the deficiency condition (`h₂` below) holds for `{x}` even if `x` has infinite
degree, so we need to assume that the vertices of `p₁` have finite degree. (The
vertices of `p₂` may have infinite degree.) With this assumption, the junk value of
`Set.ncard` does no harm in the deficiency condition: it only makes the condition
hold automatically for infinite `s`.
-/
/-- **Hall's theorem with deficiency `d`**: if the vertices of `p₁` have finite
degree and every `s ⊆ p₁` has at least `|s| - d` neighbours, then a matching covers
all but at most `d` vertices of `p₁`. -/
theorem exists_isMatching_of_forall_ncard_le_add {p₁ p₂ : Set V} {d : ℕ}
    (h₁ : G.IsBipartiteWith p₁ p₂) (hfin : ∀ x ∈ p₁, (G.neighborSet x).Finite)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard + d) :
    ∃ M : Subgraph G, M.IsMatching ∧ (p₁ \ M.verts).encard ≤ d := by
  classical
  -- each vertex of `p₁` may choose a neighbour, or one of `d` new vertices
  let N (x : p₁) : Finset V := (hfin x x.2).toFinset
  let t : p₁ → Finset (V ⊕ Fin d) := fun x => (N x).map .inl ∪ univ.map .inr
  -- Hall's condition for `t`: a nonempty `s` sees its neighbours and all `d` new
  -- vertices
  have hHall : ∀ s : Finset p₁, #s ≤ #(s.biUnion t) := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    have hs := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset,
      card_image_of_injective _ Subtype.val_injective] at hs
    have hN : (⋃ x ∈ (s.image Subtype.val : Set V), G.neighborSet x) =
        (s.biUnion N : Set V) := by
      ext; simp [N]
    rw [hN, Set.ncard_coe_finset] at hs
    have : s.biUnion t = (s.biUnion N).map .inl ∪ univ.map .inr := by
      ext (v | i)
      · simp [t]
      · simpa [t] using ⟨x₀.1, x₀.2, hx₀⟩
    rw [this, card_union_of_disjoint (disjoint_map_inl_map_inr _ _), card_map,
      card_map, card_univ, Fintype.card_fin]
    exact hs
  obtain ⟨g, hg₁, hg₂⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  exact exists_isMatching_of_injective_sum h₁ g hg₁ fun x y hxy => by
    simpa [t, N, hxy] using hg₂ x

/-!
Now let `s₀ ⊆ p₁` have the largest deficiency `d = |s₀| - |N(s₀)|`, where `N(s)` is
the open neighbourhood of `s`, i.e. `⋃ x ∈ s, G.neighborSet x`. Every `s ⊆ p₁` has at
least `|s| - d` neighbours, so there is a matching with at least `|p₁| - d` edges (by
`Subgraph.IsMatching.ncard_inter_le`). On the other hand the vertices of `p₁ \ s₀`,
together with `N(s₀)`, form a vertex cover: an edge with an endpoint in `p₁` either
starts in `p₁ \ s₀` or ends in `N(s₀)`. This vertex cover has
`|p₁| - |s₀| + |N(s₀)| = |p₁| - d` vertices, so `τ G ≤ ν G`.

[Figure: A bipartite graph with parts $p_1$ and $p_2$, in which $s_0$ has the largest deficiency $d = |s_0| - |N(s_0)| = 1$. The vertex cover $(p_1 \setminus s_0) \cup N(s_0)$ and a maximum matching both have $|p_1| - d = 4$ elements.](https://jt496.github.io/GraphTheoryInLean/figures/konig.svg)
-/
/-- **Kőnig's theorem**: in a finite bipartite graph the matching number equals the
vertex cover number. -/
theorem IsBipartite.matchingNum_eq_vertexCoverNum [Finite V] (h : G.IsBipartite) :
    ν G = τ G := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨p₁, p₂, h₁⟩ := h.exists_isBipartiteWith
  refine G.matchingNum_le_vertexCoverNum.antisymm ?_
  -- choose `s₀ ⊆ p₁` of maximum deficiency `|s₀| - |N(s₀)|`
  obtain ⟨s₀, hs₀, hmax⟩ :=
    (Set.toFinite {s : Set V | s ⊆ p₁}).toFinset.exists_max_image
      (fun s => (s.ncard : ℤ) - (⋃ x ∈ s, G.neighborSet x).ncard) ⟨∅, by simp⟩
  simp_rw [Set.Finite.mem_toFinset] at hs₀ hmax
  let N₀ := ⋃ x ∈ s₀, G.neighborSet x
  let d := s₀.ncard - N₀.ncard
  -- the deficiency of `s₀` is at least that of `∅`, which is `0`
  have h0 : N₀.ncard ≤ s₀.ncard := by simpa using hmax ∅ (Set.empty_subset _)
  obtain ⟨M, hM, hMd⟩ := exists_isMatching_of_forall_ncard_le_add (d := d) h₁
    (fun _ _ => Set.toFinite _) fun s hs => by grind
  -- `(p₁ \ s₀) ∪ N₀` is a vertex cover
  have hC : G.IsVertexCover ((p₁ \ s₀) ∪ N₀) := fun u v huv => by
    rcases h₁.mem_of_adj huv with ⟨hu, -⟩ | ⟨-, hv⟩
    · by_cases hus : u ∈ s₀
      exacts [.inr (.inr (Set.mem_biUnion hus huv)), .inl (.inl ⟨hu, hus⟩)]
    · by_cases hvs : v ∈ s₀
      exacts [.inl (.inr (Set.mem_biUnion hvs huv.symm)), .inr (.inl ⟨hv, hvs⟩)]
  -- it has at most `|p₁| - d` vertices, and `M` has at least `|p₁| - d` edges
  replace hMd : (p₁ \ M.verts).ncard ≤ d := by
    rwa [← Set.Finite.cast_ncard_eq (Set.toFinite _), Nat.cast_le] at hMd
  have := Set.ncard_union_le (p₁ \ s₀) N₀
  have := Set.ncard_sdiff_add_ncard_of_subset hs₀
  have := Set.ncard_inter_add_ncard_sdiff_eq_ncard p₁ M.verts
  have := hM.ncard_inter_le h₁
  calc τ G ≤ ((p₁ \ s₀) ∪ N₀).encard := hC.vertexCoverNum_le
    _ = ((p₁ \ s₀) ∪ N₀).ncard := (Set.Finite.cast_ncard_eq (Set.toFinite _)).symm
    _ ≤ M.edgeSet.ncard := by grind [Nat.cast_le]
    _ = M.edgeSet.encard := Set.Finite.cast_ncard_eq (Set.toFinite _)
    _ ≤ ν G := hM.le_matchingNum

/-!
The hypercube `Q[n + 1]` is bipartite (`IsBipartite.hypercube`) and has matching
number `2 ^ n` (`matchingNum_hypercube_succ`). So it also has vertex cover number
`2 ^ n`.
-/
lemma vertexCoverNum_hypercube_succ (n : ℕ) : τ Q[n + 1] = 2 ^ n := by
  rw [← (IsBipartite.hypercube _).matchingNum_eq_vertexCoverNum,
    matchingNum_hypercube_succ]

/-!
## Symmetric Differences of Matchings

The classical approach to matchings studies the symmetric difference of two
matchings. Since each vertex belongs to exactly one edge in each of two perfect
matchings `M` and `N`, every vertex of `M ∆ N` has degree `0` or `2`, so `M ∆ N` is a
union of disjoint cycles (finite or infinite) whose edges alternate between `M` and
`N`. Mathlib states this for `SimpleGraph`s rather than subgraphs, so the matchings
are first converted with `spanningCoe`.
-/
#source IsCycles -- ∀ ⦃v⦄, (G.neighborSet v).Nonempty → (G.neighborSet v).ncard = 2

/-!
Notice how the definition carefully avoids mentioning `Set.ncard = 0`, which would
allow vertices of infinite degree.
-/
#check Subgraph.IsPerfectMatching.symmDiff_isCycles
#check Subgraph.IsPerfectMatching.isAlternating_symmDiff_left

/-!
This is the machinery behind Mathlib's proof of Tutte's theorem below. Each vertex of
`M ∆ N` has no neighbours or exactly two, so by
`Walk.IsCycle.toSubgraph_eq_of_degree_le_two` every cycle in `M ∆ N` is a whole
component of `M ∆ N`. That is the easy part, since we are given the cycle. The hard
part is finding one in the first place. If `V` is finite, every non-isolated vertex
lies on a cycle whose vertices form its whole component.
-/
#check IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp

/-!
The assumption `[Finite V]` cannot be dropped. On the vertices `ℤ`, let `M` match
each even `i` with `i + 1`, and let `N` match it with `i - 1`. Then `M ∆ N` is the
two-way infinite path through all of `ℤ`, which has no cycles.

## Tutte's Theorem

*Tutte's theorem*
[Tutte 1947](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-tutte-1947)
characterizes the graphs with a perfect matching, bipartite or not. If `G` has a
perfect matching and we delete a set `U` of vertices, then each odd component of what
remains (i.e. of `G - U`) must have a vertex matched into `U`, so there are at most
`|U|` odd components. A set `U` whose deletion leaves more than `|U|` odd components
is called a *Tutte violator*. Tutte's theorem says that `G` has a perfect matching
iff there is no Tutte violator.

[Figure: A Tutte violator $U$ with three odd components of $G - U$](https://jt496.github.io/GraphTheoryInLean/figures/tutte.svg)
-/
#source SimpleGraph.IsTutteViolator

/-!
Here `G - U` is the subgraph `(⊤ : G.Subgraph).deleteVerts U`, viewed as a simple
graph via `Subgraph.coe`.

A graph with a perfect matching has no Tutte violator, and Tutte's theorem is the
converse.
-/
#check SimpleGraph.not_isTutteViolator_of_isPerfectMatching
#check SimpleGraph.tutte

/-!
Mathlib proves Tutte's theorem for `[Finite V]`. As with Hall's condition, the
definition of a Tutte violator uses `Set.ncard`, which is `0` on infinite
sets. So in an infinite graph, deleting every vertex but one, `x`, gives a Tutte
violator: the infinite set `{x}ᶜ` has `Set.ncard` equal to `0`, while `x` alone
forms one odd component. This is an accident of the junk value, but the classical
theorem fails for infinite graphs too. In `subdividedStar ℕ` from the Hall section,
deleting any finite set `U` leaves at most `|U|` finite odd components, yet there is
no perfect matching (`not_exists_isPerfectMatching_subdividedStar`).

# Turán's Theorem, Stability and Asymptotics

Extremal graph theory asks how many edges a graph on `n` vertices can have while
avoiding a given subgraph. The foundational result is *Turán's theorem*, which
answers this question when the forbidden subgraph is a complete graph. Recall from
[Cliques](#chapter-cliques) that `G.CliqueFree (r + 1)` says that `G` has no
clique of size `r + 1`.

## Turán Graphs

The extremal graphs are the *Turán graphs*. Mathlib defines `turanGraph n r` on
`Fin n`, and we introduce the notation `T[n, r]`.

[Figure: The Turán graph $T(10, 3)$](https://jt496.github.io/GraphTheoryInLean/figures/turan.svg)
-/
#source turanGraph

/-- `T[n, r]` is the Turán graph `turanGraph n r`: the complete `r`-partite graph on
`Fin n` whose parts are the residue classes modulo `r`. -/
scoped notation "T[" n ", " r "]" => turanGraph n r

/-!
Two vertices of `T[n, r]` are adjacent iff they have different residues modulo
`r`, so it is the complete `r`-partite graph whose parts are the residue classes.
These parts are *balanced*: any two differ in size by at most one, since the residue
classes of `0, …, n - 1` modulo `r` have sizes `⌊n / r⌋` or `⌈n / r⌉`. In Mathlib's
terms they form an *equipartition* (`Finpartition.IsEquipartition`, defined using
`Set.EquitableOn`). For example, when `r` divides `n` the Turán graph `T[n, r]` is
isomorphic to Mathlib's `completeEquipartiteGraph r (n / r)`, which has `r` parts
of size `n / r`.
-/
#check completeEquipartiteGraph.turanGraph

/-!
The case `r = 0` is a junk value. Since `a % 0 = a` in Lean, any two distinct
vertices are adjacent in `T[n, 0]`, so `T[n, 0] = K[n]`. Most results about Turán
graphs assume `0 < r`.
-/
example (n : ℕ) : T[n, 0] = K[n] := by
  simp

/-!
For instance, a graph is `1`-clique-free iff it has no vertices, so `T[n, 0]` is not
`1`-clique-free when `0 < n`.
-/
#check cliqueFree_one
#check turanGraph_cliqueFree -- 0 < r → T[n, r].CliqueFree (r + 1)

/-!
The number of edges of `T[n, r]` is called `turanNumber n r`. Turán graphs have
decidable adjacency, so we can compute it.
-/
#eval turanNumber 10 3 -- 33
#check turanNumber_eq

/-!
In particular `turanNumber n r` is at most `(1 - 1 / r) * n ^ 2 / 2`.
-/
#check mul_turanNumber_le -- 2 * r * turanNumber n r ≤ (r - 1) * n ^ 2

/-!
## Turán's Theorem

Mathlib calls a graph `G` *Turán-maximal* if it is `(r + 1)`-clique-free and has at
least as many edges as any other `(r + 1)`-clique-free graph on the same vertices.
This is a special case of `IsExtremal`, which says that a graph has the most edges
among the graphs on its vertex type with a given property.
-/
#source IsExtremal
#source IsTuranMaximal

/-!
Turán's theorem
[Turán 1941](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-turan-1941)
says that for `0 < r` the Turán-maximal graphs are exactly the graphs isomorphic to
the Turán graph.
-/
#check isTuranMaximal_iff_nonempty_iso_turanGraph

example (n : ℕ) : T[n, 4].IsTuranMaximal 4 :=
  isTuranMaximal_turanGraph (by decide)

/-!
The version of Turán's theorem that is usually quoted is the resulting upper bound on
the number of edges.
-/
#check CliqueFree.card_edgeFinset_le

/-!
In terms of the clique number `ω` (`cliqueNum`): a finite graph with `ω G ≤ r` has no
`(r + 1)`-clique, so it has at most `turanNumber n r` edges.
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ} (h : ω G ≤ r) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) r :=
  CliqueFree.card_edgeFinset_le fun s hs => by
    have := hs.le_cliqueNum
    grind

/-!
### Mantel's Theorem

The case `r = 2` of Turán's theorem is *Mantel's theorem*
[Mantel 1907](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-mantel-1907):
a triangle-free graph on `n` vertices has at most `⌊n² / 4⌋` edges. Equality holds
for the balanced complete bipartite graph `T[n, 2]`.
-/
#check turanNumber_two -- turanNumber n 2 = n ^ 2 / 4

/-!
By `CliqueFree.mycielskian`, the Mycielskian of a triangle-free graph on `n` vertices
is a triangle-free graph on `2 * n + 1` vertices, so Mantel's theorem bounds its
number of edges by `(2 * n + 1) ^ 2 / 4`.
-/
example [Fintype V] [DecidableRel G.Adj] (h3 : G.CliqueFree 3) :
    #mμ(G).edgeFinset ≤ (2 * Fintype.card V + 1) ^ 2 / 4 := by
  convert CliqueFree.card_edgeFinset_le h3.mycielskian
  simp [two_mul, turanNumber_two]

/-!
## Proof of Turán's Theorem

Mathlib's proof of Turán's theorem uses *Zykov symmetrization*: replacing a vertex
`t` by a copy of a non-adjacent vertex `s` (giving `t` exactly the neighbours of `s`)
cannot create an `(r + 1)`-clique, and it removes the edges at `t` while adding as
many edges as `s` has. This operation is `replaceVertex`. In a Turán-maximal graph no
such replacement can increase the number of edges, so non-adjacent vertices have the
same degree (`IsTuranMaximal.degree_eq_of_not_adj`). It follows that non-adjacency is
transitive (`IsTuranMaximal.not_adj_trans`), so the graph is complete multipartite
(`IsCompleteMultipartite`).

[Figure: Left: a graph with non-adjacent vertices $s$ and $t$. Right: `G.replaceVertex s t`.](https://jt496.github.io/GraphTheoryInLean/figures/replace_vertex.svg)
-/
#source replaceVertex

/-!
Mathlib finishes its proof of Turán's theorem by showing that a Turán-maximal graph,
which is now known to be complete multipartite, is isomorphic to the Turán graph.
-/
#check IsTuranMaximal.nonempty_iso_turanGraph

/-!
It does this through a series of lemmas about the parts of the graph, such as
`IsTuranMaximal.card_parts`. Besides being `(r + 1)`-clique-free, the argument only
needs three properties of a Turán-maximal graph: it is complete multipartite, its
parts are balanced, and it has an `r`-clique unless it is complete. We state this
last one as `∀ x y, x ≠ y → ¬G.Adj x y → ¬G.CliqueFree r` (the hypothesis `hsat`
below), which is how the argument uses it. For a Turán-maximal graph, adding the
edge `x — y` creates an `(r + 1)`-clique, and removing `x` from it leaves an
`r`-clique in `G`. Below we reprove Mathlib's lemmas for any complete multipartite
graph with these properties, following Mathlib's proofs very closely (often
verbatim). We will need these results for
[Zykov's theorem](#section-zykov-s-theorem).

The parts of a finite complete multipartite graph form a `Finpartition` of its
vertices, whose parts are the equivalence classes of non-adjacency
(`IsCompleteMultipartite.setoid`).
-/
namespace IsCompleteMultipartite
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance (hc : G.IsCompleteMultipartite) : DecidableRel hc.setoid.r :=
  inferInstanceAs (DecidableRel (¬G.Adj · ·))

/-- The parts of a finite complete multipartite graph, as a `Finpartition` of its
vertices. -/
def finpartition (hc : G.IsCompleteMultipartite) : Finpartition (univ : Finset V) :=
  Finpartition.ofSetoid hc.setoid

/-!
Two vertices are non-adjacent iff they lie in the same part.
-/
lemma not_adj_iff_part_eq (hc : G.IsCompleteMultipartite) {s t : V} :
    ¬G.Adj s t ↔ hc.finpartition.part s = hc.finpartition.part t := by
  change hc.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change t ∈ hc.finpartition.part s ↔ _
  rw [hc.finpartition.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s), eq_comm]

/-!
The part of `v` consists of the non-neighbours of `v`.
-/
lemma part_finpartition (hc : G.IsCompleteMultipartite) (v : V) :
    hc.finpartition.part v = ({x | ¬G.Adj v x} : Finset V) := by
  ext x
  simp [finpartition, Finpartition.mem_part_ofSetoid_iff_rel, setoid]

/-!
If the parts are balanced, they form an equipartition.
-/
lemma isEquipartition (hc : G.IsCompleteMultipartite)
    (hbal : ∀ v w, #{x | ¬G.Adj w x} ≤ #{x | ¬G.Adj v x} + 1) :
    hc.finpartition.IsEquipartition := by
  intro large small hl hs
  obtain ⟨w, hw⟩ := hc.finpartition.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := hc.finpartition.nonempty_of_mem_parts hs
  rw [← hc.finpartition.part_eq_of_mem hl hw, ← hc.finpartition.part_eq_of_mem hs hv,
    part_finpartition, part_finpartition]
  exact hbal v w

/-!
An `(r + 1)`-clique-free complete multipartite graph has at most `r` parts, since
one vertex from each part gives a clique.
-/
lemma card_parts_le (hc : G.IsCompleteMultipartite) {r : ℕ}
    (hcf : G.CliqueFree (r + 1)) :
    #hc.finpartition.parts ≤ r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := hc.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ ?_, rfl⟩
    contrapose hn
    exact hz.injOn hv hw (by rwa [← hc.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (hcf.mono (Nat.succ_le_of_lt l)) ncf

/-!
If `G` has an `r`-clique unless it is complete, then it has exactly `min n r`
parts, where `n` is the number of vertices.
-/
lemma card_parts (hc : G.IsCompleteMultipartite) {r : ℕ} (hcf : G.CliqueFree (r + 1))
    (hsat : ∀ x y, x ≠ y → ¬G.Adj x y → ¬G.CliqueFree r) :
    #hc.finpartition.parts = min (Fintype.card V) r := by
  refine le_antisymm (le_min hc.finpartition.card_parts_le_card
    (hc.card_parts_le hcf)) ?_
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to l.1
    fun a _ ↦ hc.finpartition.part_mem.2 (mem_univ a)
  apply hsat x y hn (hc.not_adj_iff_part_eq.2 he)
  intro z hz
  have hinj : Set.InjOn hc.finpartition.part (z : Set V) := fun a ha b hb hab =>
    by_contra fun hne => hc.not_adj_iff_part_eq.2 hab (hz.1 ha hb hne)
  exact l.2.not_ge (hz.card_eq ▸ card_le_card_of_injOn _
    (fun a _ => hc.finpartition.part_mem.2 (mem_univ a)) hinj)

/-!
Vertices whose parts have different sizes lie in different parts and so are adjacent.
-/
omit [DecidableEq V]
lemma adj_of_card_ne (hc : G.IsCompleteMultipartite) {v w : V}
    (hne : #{x | ¬G.Adj v x} ≠ #{x | ¬G.Adj w x}) : G.Adj v w := by
  by_contra hn
  refine hne (congrArg card ?_)
  ext x
  simp_rw [mem_filter, mem_univ, true_and]
  exact ⟨hc.trans _ _ _ fun h => hn h.symm, hc.trans _ _ _ hn⟩

/-!
A complete multipartite `(r + 1)`-clique-free graph with balanced parts, which has an
`r`-clique unless it is complete, is isomorphic to the Turán graph.
-/
theorem nonempty_iso_turanGraph {r : ℕ} (hc : G.IsCompleteMultipartite)
    (hcf : G.CliqueFree (r + 1))
    (hbal : ∀ v w, #{x | ¬G.Adj w x} ≤ #{x | ¬G.Adj v x} + 1)
    (hsat : ∀ x y, x ≠ y → ¬G.Adj x y → ¬G.CliqueFree r) :
    Nonempty (G ≃g T[Fintype.card V, r]) := by
  classical
  -- number the vertices so that the parts are the residue classes
  obtain ⟨zm, zp⟩ := (hc.isEquipartition hbal).exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans (zm.trans (finCongr card_univ))
  intro a b
  simp_rw [turanGraph_adj, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply,
    finCongr_apply, Fin.val_cast]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← hc.not_adj_iff_part_eq] at this
  rw [← not_iff_not, not_ne_iff, this, hc.card_parts hcf hsat]
  rcases le_or_gt r (Fintype.card V) with c | c
  · rw [min_eq_right c]
  · have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ x⟩).2
    rw [min_eq_left c.le, Nat.mod_eq_of_lt (lc a), Nat.mod_eq_of_lt (lc b),
      Nat.mod_eq_of_lt ((lc a).trans c), Nat.mod_eq_of_lt ((lc b).trans c)]

end IsCompleteMultipartite

/-!
## Füredi's Stability Theorem

Turán's theorem says that, up to isomorphism, the Turán graph is the only
`(r + 1)`-clique-free graph on `n` vertices with `turanNumber n r` edges. A
*stability theorem* says that any `(r + 1)`-clique-free graph with "almost" this many
edges is "almost" the Turán graph, where the exact meaning of "almost" can vary.

Füredi
[Füredi 2015](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-furedi-2015)
gave a short proof of a stability theorem in which being "almost" the Turán graph
means becoming `r`-colourable after deleting a few edges. If `G` is
`(r + 1)`-clique-free and has `turanNumber n r - t` edges, then deleting at most `t`
edges of `G` leaves an `r`-colourable graph. We prove this below in an additive form:
there is a set `s` of edges of `G` such that `G.deleteEdges s` is `r`-colourable and
`e(G) + #s ≤ turanNumber n r`, where `e(G)` is the number of edges of `G`.

The proof idea goes back to Erdős
[Erdős 1970](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-erdos-1970).
Pick a vertex `x` of maximum degree and put all of its non-neighbours (including `x`
itself) into one part. Each of them has at most `deg x` neighbours, which is the
number of vertices outside their part. Then continue inside the neighbourhood of `x`,
which is `r`-clique-free since `x` is adjacent to all of it. Erdős used this to show
that `G` has at most as many edges as the complete `r`-partite graph with these
parts. Füredi's observation is that the same argument leaves enough room to also
count the edges of `G` with both endpoints in the same part.

To make the induction on `r` work we prove a statement about a set `S` of vertices
that contains no `(r + 1)`-clique, and record the parts as the colour classes of a
function `c : V → ℕ` taking values less than `r` on `S`. Degrees are now taken within
`S`: for `v ∈ S` the number of neighbours of `v` in `S` is `G.degIn S v` (see
`degIn`), and `x` is chosen to maximize this. Then the key inequality is:

`∑ v ∈ S, (G.degIn S v + #{w ∈ S | G.Adj v w ∧ c w = c v})` is at most
`∑ v ∈ S, #{w ∈ S | c w ≠ c v}`.

The left-hand side is twice the number of edges in `S` plus twice the number of
*monochromatic* edges in `S`, those whose endpoints have the same colour. The
right-hand side is twice the number of edges of the complete multipartite graph on
`S` whose parts are the colour classes. For `S = V`, let `s` be the set of
monochromatic edges of `G`, so that `G.deleteEdges s` is `r`-colourable. Then the
left-hand side is `2 * e(G) + 2 * #s`, and Turán's theorem bounds the right-hand side
by `2 * turanNumber n r`. Dividing by `2` gives Füredi's theorem as stated above.

In the induction step we split `S` into `N = S ∩ N(x)`, the neighbours of `x` in `S`,
and the set `Vᵣ` of non-neighbours of `x` in `S`. We colour `Vᵣ` with the new colour
`r`. Each of the three sums over `S` then splits into four blocks, according to
whether `v` and `w` lie in `N` or in `Vᵣ`.

[Figure: $V_r$ ($x$ and its non-neighbours) gets colour $r$ (orange). In $N$, $x'$ and its non-neighbours get $r - 1$ (green) and $N'$ is coloured recursively (blue). Dashed edges are monochromatic](https://jt496.github.io/GraphTheoryInLean/figures/furedi.svg)
-/
lemma _root_.Finset.sum_card_filter_union [DecidableEq V] {s t : Finset V}
    (h : Disjoint s t) (p : V → V → Prop) [DecidableRel p] :
    ∑ v ∈ s ∪ t, #{w ∈ s ∪ t | p v w} =
      ∑ v ∈ s, #{w ∈ s | p v w} + ∑ v ∈ s, #{w ∈ t | p v w} +
        ∑ v ∈ t, #{w ∈ s | p v w} + ∑ v ∈ t, #{w ∈ t | p v w} := by
  simp [sum_union h, filter_union, card_union_of_disjoint (disjoint_filter_filter h),
        sum_add_distrib, add_assoc]

/-!
The edges between `N` and `Vᵣ` are counted once from each side, and the
double-counting lemma `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` says that
the two counts agree.
-/
lemma sum_degIn_comm [DecidableRel G.Adj] (s t : Finset V) :
    ∑ v ∈ s, G.degIn t v = ∑ v ∈ t, G.degIn s v := by
  simpa [degIn, bipartiteAbove, bipartiteBelow, adj_comm] using
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s) (t := t) G.Adj

/-!
The induction step only uses that `Vᵣ` is a new colour class whose vertices have at
most `#N` neighbours in `S`, which holds because `x` has maximum degree. We state it
for any disjoint `N` and `Vᵣ` and a colouring `c` that is less than `r` on `N` and
equal to `r` on `Vᵣ`.
-/
private lemma furedi_step [DecidableRel G.Adj] [DecidableEq V] {N Vᵣ : Finset V}
    {c : V → ℕ} {r : ℕ} (hNV : Disjoint N Vᵣ) (hN : ∀ v ∈ N, c v < r)
    (hV : ∀ v ∈ Vᵣ, c v = r)
    (hdeg : ∀ v ∈ Vᵣ, G.degIn (N ∪ Vᵣ) v ≤ #N)
    (hc : ∑ v ∈ N, (G.degIn N v + #{w ∈ N | G.Adj v w ∧ c w = c v}) ≤
      ∑ v ∈ N, #{w ∈ N | c w ≠ c v}) :
    ∑ v ∈ N ∪ Vᵣ, (G.degIn (N ∪ Vᵣ) v + #{w ∈ N ∪ Vᵣ | G.Adj v w ∧ c w = c v}) ≤
      ∑ v ∈ N ∪ Vᵣ, #{w ∈ N ∪ Vᵣ | c w ≠ c v} := by
  -- colours on `N` differ from those on `Vᵣ`, which all equal `r`
  have hne : ∀ v ∈ N, ∀ w ∈ Vᵣ, c v ≠ c w := fun v hv w hw => by
    rw [hV w hw]; exact (hN v hv).ne
  -- monochromatic edges: none between `N` and `Vᵣ`, and every edge inside `Vᵣ`
  have m1 : ∑ v ∈ N, #{w ∈ Vᵣ | G.Adj v w ∧ c w = c v} = 0 :=
    sum_eq_zero fun v hv => card_eq_zero.2 <| filter_false_of_mem fun w hw h =>
      hne v hv w hw h.2.symm
  have m2 : ∑ v ∈ Vᵣ, #{w ∈ N | G.Adj v w ∧ c w = c v} = 0 :=
    sum_eq_zero fun v hv => card_eq_zero.2 <| filter_false_of_mem fun w hw h =>
      hne w hw v hv h.2
  have m3 : ∑ v ∈ Vᵣ, #{w ∈ Vᵣ | G.Adj v w ∧ c w = c v} = ∑ v ∈ Vᵣ, G.degIn Vᵣ v :=
    sum_congr rfl fun v hv => congrArg card <| filter_congr fun w hw => by
      simp [hV v hv, hV w hw]
  -- pairs of different colours: every pair between `N` and `Vᵣ`, none inside `Vᵣ`
  have d1 : ∑ v ∈ N, #{w ∈ Vᵣ | c w ≠ c v} = #N * #Vᵣ := by
    rw [sum_const_nat fun v hv => congrArg card <| filter_true_of_mem fun w hw =>
      (hne v hv w hw).symm]
  have d2 : ∑ v ∈ Vᵣ, #{w ∈ N | c w ≠ c v} = #Vᵣ * #N := by
    rw [sum_const_nat fun v hv => congrArg card <| filter_true_of_mem fun w hw =>
      hne w hw v hv]
  have d3 : ∑ v ∈ Vᵣ, #{w ∈ Vᵣ | c w ≠ c v} = 0 :=
    sum_eq_zero fun v hv => card_eq_zero.2 <| filter_false_of_mem fun w hw h =>
      h (by rw [hV v hv, hV w hw])
  -- the vertices of `Vᵣ` have at most `#N` neighbours in `N ∪ Vᵣ`
  have hD : ∑ v ∈ Vᵣ, G.degIn N v + ∑ v ∈ Vᵣ, G.degIn Vᵣ v ≤ #Vᵣ * #N := by
    rw [← sum_add_distrib, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun v hv => (degIn_union _ _ _ hNV).symm.le.trans (hdeg v hv)
  have e1 := sum_card_filter_union hNV G.Adj
  have e2 := sum_card_filter_union hNV (fun v w => G.Adj v w ∧ c w = c v)
  have e3 := sum_card_filter_union hNV (fun v w => c w ≠ c v)
  have hdc := sum_degIn_comm (G := G) N Vᵣ
  simp_rw [degIn_eq_card_filter, sum_add_distrib] at *
  grind

/-!
The local form of Füredi's inequality, proved by induction on `r`. A set `S` with no
`(r + 1)`-clique has a colouring `c`, taking values less than `r` on `S`, with the
following property. Count the edges of `G` in `S`, counting the monochromatic ones
twice: the total is at most the number of edges of the complete multipartite graph
whose parts are the colour classes.
-/
private lemma furedi_aux [DecidableRel G.Adj] (r : ℕ) :
    ∀ S : Finset V, (∀ t ⊆ S, ¬ G.IsNClique (r + 1) t) →
      ∃ c : V → ℕ, (∀ v ∈ S, c v < r) ∧
        ∑ v ∈ S, (G.degIn S v + #{w ∈ S | G.Adj v w ∧ c w = c v}) ≤
          ∑ v ∈ S, #{w ∈ S | c w ≠ c v} := by
  classical
  induction r with
  | zero =>
    -- a set with no `1`-clique is empty
    intro S hS
    obtain rfl : S = ∅ :=
      eq_empty_of_forall_notMem fun x hx => hS {x} (by simpa) (by simp)
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ r ih =>
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp, by simp⟩
    -- `x` has maximum degree into `S`; split `S` into `N = S ∩ N(x)` and the rest
    obtain ⟨x, hxS, hx⟩ := exists_max_image S (G.degIn S) hne
    set N := {w ∈ S | G.Adj x w}
    set Vᵣ := {w ∈ S | ¬ G.Adj x w}
    have hdisj : Disjoint N Vᵣ := disjoint_filter_filter_not _ _ _
    have huni : N ∪ Vᵣ = S := filter_union_filter_not_eq _ _
    -- `N` has no `(r + 1)`-clique, since `x` would extend it to an `(r + 2)`-clique
    have hN : ∀ t ⊆ N, ¬ G.IsNClique (r + 1) t := fun t ht hc =>
      hS (insert x t) (insert_subset hxS (ht.trans (filter_subset _ _)))
        (hc.insert fun w hw => (mem_filter.1 (ht hw)).2)
    obtain ⟨c', hc'r, hc'⟩ := ih N hN
    -- colour `N` by `c'` and `Vᵣ` by the new colour `r`
    let c : V → ℕ := N.piecewise c' fun _ => r
    have hcN : ∀ v ∈ N, c v = c' v := fun v hv => piecewise_eq_of_mem _ _ _ hv
    have hcr : ∀ v ∈ N, c v < r := fun v hv => hcN v hv ▸ hc'r v hv
    have hcV : ∀ v ∈ Vᵣ, c v = r := fun v hv =>
      piecewise_eq_of_notMem _ _ _ (disjoint_right.1 hdisj hv)
    refine ⟨c, fun v hv => ?_, ?_⟩
    · rcases mem_union.1 (huni ▸ hv) with h | h
      · exact (hcr v h).trans r.lt_succ_self
      · exact (hcV v h).trans_lt r.lt_succ_self
    rw [← huni]
    refine furedi_step hdisj hcr hcV (fun v hv => huni ▸ hx v (mem_filter.1 hv).1) ?_
    -- on `N` the colouring `c` agrees with `c'`
    have h1 : ∀ v ∈ N, #{w ∈ N | G.Adj v w ∧ c w = c v} =
        #{w ∈ N | G.Adj v w ∧ c' w = c' v} := fun v hv =>
      congrArg card (filter_congr fun w hw => by rw [hcN v hv, hcN w hw])
    have h2 : ∀ v ∈ N, #{w ∈ N | c w ≠ c v} = #{w ∈ N | c' w ≠ c' v} := fun v hv =>
      congrArg card (filter_congr fun w hw => by rw [hcN v hv, hcN w hw])
    calc _ = _ := sum_congr rfl fun v hv => by rw [h1 v hv]
      _ ≤ _ := hc'
      _ = _ := (sum_congr rfl h2).symm

/-!
In the proof below the complete `r`-partite graph is `K`, in which two vertices are
adjacent iff they have different colours. Deleting the monochromatic edges of `G`
leaves `G ⊓ K`.
-/
/-- **Füredi's stability theorem**: an `(r + 1)`-clique-free graph `G` on `n`
vertices can be made `r`-colourable by deleting at most `turanNumber n r - e(G)`
edges. -/
theorem CliqueFree.exists_colorable_deleteEdges [Fintype V] [DecidableRel G.Adj]
    {r : ℕ} (h : G.CliqueFree (r + 1)) :
    ∃ s ⊆ G.edgeFinset, (G.deleteEdges s).Colorable r ∧
      #G.edgeFinset + #s ≤ turanNumber (Fintype.card V) r := by
  classical
  obtain ⟨c, hcr, hc⟩ := furedi_aux (G := G) r univ fun t _ ht => h t ht
  -- the complete multipartite graph whose parts are the colour classes of `c`
  let K : SimpleGraph V := (⊤ : SimpleGraph ℕ).comap c
  have hK : ∀ u v, K.Adj u v ↔ c u ≠ c v := fun u v => by simp [K]
  have hKcol : K.Colorable r :=
    ⟨Coloring.mk (fun v => (⟨c v, hcr v (mem_univ v)⟩ : Fin r)) fun {u v} huv => by
      simpa [Fin.ext_iff] using (hK u v).1 huv⟩
  have hle : G ⊓ K ≤ G := inf_le_left
  -- delete the edges of `G` that are not edges of `G ⊓ K`
  refine ⟨G.edgeFinset \ (G ⊓ K).edgeFinset, sdiff_subset, ?_, ?_⟩
  · rw [coe_sdiff, coe_edgeFinset, coe_edgeFinset, deleteEdges_sdiff_eq_of_le hle]
    exact hKcol.mono_left inf_le_right
  have hdeg (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
      H.degree v = #{w | H.Adj v w} := by
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have dK : ∀ v, K.degree v = #{w | c w ≠ c v} := fun v => by
    simp [hdeg, hK, eq_comm]
  -- `deg_G v` splits into the edges of `G ⊓ K` at `v` and the monochromatic ones
  have dG : ∀ v, G.degree v = (G ⊓ K).degree v + #{w | G.Adj v w ∧ c w = c v} :=
    fun v => by
      rw [hdeg, hdeg]
      simpa [inf_adj, hK, filter_filter, eq_comm] using
        (card_filter_add_card_filter_not (s := {w | G.Adj v w})
          (fun w => c w ≠ c v)).symm
  have e1 :
      ∑ v, G.degree v + ∑ v, #{w | G.Adj v w ∧ c w = c v} ≤ ∑ v, K.degree v := by
    simp_rw [← sum_add_distrib, dK, hdeg G]
    exact hc
  have e2 : ∑ v, G.degree v =
      ∑ v, (G ⊓ K).degree v + ∑ v, #{w | G.Adj v w ∧ c w = c v} := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ => dG v
  have := (hKcol.cliqueFree (Nat.lt_succ_self r)).card_edgeFinset_le
  have := sum_degrees_eq_twice_card_edges K
  have := sum_degrees_eq_twice_card_edges G
  -- our primed version accepts the `Fintype (G ⊓ K).edgeSet` instance found here
  have := sum_degrees_eq_twice_card_edges' (G ⊓ K)
  have := card_sdiff_of_subset (edgeFinset_mono hle)
  grind

/-!
Dropping `#s`, we recover the edge bound of Turán's theorem. This is not an
independent proof, since Füredi's theorem used that bound for the graph `K`.
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1)) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) r := by
  obtain ⟨s, -, -, hs⟩ := h.exists_colorable_deleteEdges
  grind

/-!
For `r = 2` this is a stability version of Mantel's theorem: a triangle-free graph on
`n` vertices with at least `n ^ 2 / 4 - t` edges can be made bipartite by deleting at
most `t` edges.
-/
example [Fintype V] [DecidableRel G.Adj] {t : ℕ} (h : G.CliqueFree 3)
    (he : Fintype.card V ^ 2 / 4 - t ≤ #G.edgeFinset) :
    ∃ s ⊆ G.edgeFinset, (G.deleteEdges s).IsBipartite ∧ #s ≤ t := by
  obtain ⟨s, hs, hcol, hle⟩ := h.exists_colorable_deleteEdges (r := 2)
  rw [turanNumber_two] at hle
  exact ⟨s, hs, hcol, by grind⟩

/-!
Mathlib has a name for the opposite situation: `G.DeleteFar p t` says that at least
`t` edges *must* be deleted from `G` to get a graph with property `p`. The threshold
`t` lives in an ordered ring rather than `ℕ`, so that it can be `ε * n ^ 2` with `ε`
real, as in `FarFromTriangleFree` below.
-/
#source DeleteFar

/-!
In these terms, Füredi's theorem says that if at least `t` edges must be deleted to
make an `(r + 1)`-clique-free graph `r`-colourable, then it has at most
`turanNumber n r - t` edges.
-/
example [Fintype V] [DecidableRel G.Adj] {r t : ℕ} (h : G.CliqueFree (r + 1))
    (hfar : G.DeleteFar (fun H => H.Colorable r) (t : ℤ)) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) r - t := by
  obtain ⟨s, hs, hcol, hle⟩ := h.exists_colorable_deleteEdges
  have := hfar hs hcol
  grind

/-!
## The Andrásfai–Erdős–Sós Theorem

Turán's theorem says that the densest `(r + 1)`-clique-free graphs are Turán graphs,
while Füredi's stability theorem tells us that graphs that are almost extremal, in
terms of number of edges, are almost `r`-colourable.

The Andrásfai–Erdős–Sós theorem
[Andrásfai–Erdős–Sós 1974](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-andrasfai-erdos-sos-1974)
gives a different type of stability result related to the minimum degree: any
`(r + 1)`-clique-free graph with minimum degree greater than
`(3 * r - 4) * n / (3 * r - 1)` must be `r`-colourable. For `r = 2` this says that a
triangle-free graph with minimum degree greater than `2 * n / 5` is bipartite. The
uniform blow-up `C[5][t]` shows that `2 * n / 5` cannot be lowered (Exercise 12).

[Figure: The $3$-uniform blow-up of $C_5$: a non-bipartite triangle-free graph with minimum degree $2n/5$](https://jt496.github.io/GraphTheoryInLean/figures/blowup_c5.svg)
-/
#check colorable_of_cliqueFree_lt_minDegree

/-!
Put the other way round: a triangle-free graph that contains an odd closed walk, and
so is not bipartite (`isBipartite_iff_forall_walk_even_length`), has minimum degree
at most `2 * n / 5`.
-/
example [Fintype V] [DecidableRel G.Adj] (h3 : G.CliqueFree 3) {u : V}
    (w : G.Walk u u) (hw : Odd w.length) : δ(G) ≤ 2 * Fintype.card V / 5 := by
  by_contra! h
  have hb : G.IsBipartite := colorable_of_cliqueFree_lt_minDegree h3 h
  exact Nat.not_even_iff_odd.2 hw (isBipartite_iff_forall_walk_even_length.1 hb u w)

/-!
## Extremal Numbers

Turán's theorem answers the extremal question for complete graphs. For a general
forbidden graph `H`, the *extremal number* `extremalNumber n H` is the maximum number
of edges in an `H`-free graph on `n` vertices. Recall that `H.Free G` means that `G`
contains no copy of `H`. Mathlib defines `extremalNumber` as a supremum over all
graphs on `Fin n`.
-/
#source extremalNumber -- sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

/-!
Although this is a supremum over a finite set, `extremalNumber` is `noncomputable`.
The definition opens `Classical` and uses it twice: to count the edges of each graph
`G : SimpleGraph (Fin n)` in the supremum, and to decide whether `G` is `H`-free.
Instance arguments cannot help with the first: `G` is bound by the supremum rather
than being an argument of `extremalNumber`, so there is nowhere to supply
`DecidableRel G.Adj`. A computable version could instead maximize over edge sets
`s : Finset (Sym2 (Fin n))`, since Lean can decide adjacency in the graph
`fromEdgeSet s` with these edges. For the second, Mathlib has no
`Decidable (H ⊑ G)` instance, but one can be written by searching all maps
`W → Fin n` for an injective homomorphism, given `Fintype W`, `DecidableEq W` and
`DecidableRel H.Adj`. Such a version would be extremely slow, checking up to
`2 ^ n.choose 2 * n ^ |W|` pairs of an edge set and a map.

The key facts about it are the following results.
-/
#check card_edgeFinset_le_extremalNumber
#check IsContained.of_extremalNumber_lt_card_edgeFinset
#check extremalNumber_le_iff

/-!
Turán's theorem, restated in this language, computes the extremal numbers of
complete graphs.
-/
#check extremalNumber_top
#check card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph

/-!
For bipartite forbidden graphs the extremal numbers are much smaller. The
*Zarankiewicz number*
[Zarankiewicz 1951](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-zarankiewicz-1951)
(`zarankiewicz`) is the maximum number of edges in a `K[s, t]`-free bipartite graph
with parts of sizes `m` and `n`.
-/
#source zarankiewicz
#check zarankiewicz_le_extremalNumber
#check two_mul_extremalNumber_le_zarankiewicz_symm

/-!
The main upper bound for these numbers, the *Kővári–Sós–Turán theorem*
[Kővári–Sós–Turán 1954](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-kovari-sos-turan-1954),
says that `extremalNumber n K[s, t] = O(n ^ (2 - 1 / s))`. This is not yet in
Mathlib.

## Turán Density and the Erdős–Stone Theorem

How does `extremalNumber n H` grow with `n`? Dividing by the number of possible edges
`n.choose 2` gives a sequence that is decreasing and so converges. Its limit is the
*Turán density* (`turanDensity`).

Statements about limits in Mathlib use filters:
`Tendsto f atTop (𝓝 a)` says that `f n → a` as `n → ∞`.
-/
section asymptotics
open Filter Asymptotics
#source turanDensity
#check tendsto_turanDensity

/-!
When the Turán density is nonzero, `extremalNumber n H` is asymptotically
`turanDensity H * n.choose 2`, which Mathlib writes with `~[atTop]`
(asymptotic equivalence).
-/
#check isEquivalent_extremalNumber -- ex (n, H) ~ H.turanDensity * n.choose 2

/-!
Phrases like "for all sufficiently large `n`" are written with `∀ᶠ (n : ℕ) in atTop`.
For example, for any `ε > 0`, every large enough graph with at least
`(H.turanDensity + ε) * n.choose 2` edges contains a copy of `H`.
-/
#check eventually_isContained_of_card_edgeFinset

/-!
The *Erdős–Stone theorem*
[Erdős–Stone 1946](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-erdos-stone-1946)
says that a large graph whose density is a little above `1 - 1 / r`, the Turán
density of `K[r + 1]` (by Turán's theorem), contains not just `K[r + 1]` but a
complete `(r + 1)`-partite graph with large parts:
`completeEquipartiteGraph (r + 1) t`.

Mathlib has the minimum degree version of this theorem.
-/
#check eventually_completeEquipartiteGraph_isContained_of_minDegree

end asymptotics

/-!
The Erdős–Stone–Simonovits formula
[Erdős–Simonovits 1966](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-erdos-simonovits-1966),
which follows from the Erdős–Stone theorem, is not yet in Mathlib: if `χ H = r + 2`
then `turanDensity H = 1 - 1 / (r + 1)`. (Writing `r + 2` excludes an `H` with no
edges: it is contained in every large graph, so its Turán density is `0`, while
`1 - 1 / 0 = 1` in Lean.)

# Zykov's Theorem *

Turán's theorem bounds the number of edges of an `(r + 1)`-clique-free graph. An edge
is just a `2`-clique, and Zykov
[Zykov 1949](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-zykov-1949)
proved the following generalization: any `(r + 1)`-clique-free graph on `n` vertices
has at most as many `s`-cliques as the Turán graph `T[n, r]`. Moreover, except for
the degenerate cases of `s < 2`, `s > r` or `s > n`, the Turán graph is (up to
isomorphism) the unique maximizer.

For example, `T[7, 3]` is `4`-clique-free and its parts have sizes `3`, `2` and `2`,
so it has `3 * 2 * 2 = 12` triangles. Zykov's theorem says that no `4`-clique-free
graph on `7` vertices has more triangles than this, and any `4`-clique-free graph on
`7` vertices with this many triangles is isomorphic to `T[7, 3]`.
-/
#eval #(T[7, 3].cliqueFinset 3) -- 12

/-!
Nothing later in the chapter depends on the proof below, so a reader who only wants
the statement can go straight to
[Regularity and Removal](#section-regularity-and-removal) or
[Infinite Graphs](#section-infinite-graphs).

The proof follows the same basic strategy as Mathlib's proof of Turán's theorem (by
Zykov symmetrization), but we have to work a bit harder.

Fix `s ≥ 2` and let `G` have the most `s`-cliques among the `(r + 1)`-clique-free
graphs on `V`. We show in turn that `G` is complete multipartite, that its parts are
balanced, and that it has an `r`-clique unless it is complete. Then, as we proved
above, such a graph is isomorphic to `T[n, r]`
(`IsCompleteMultipartite.nonempty_iso_turanGraph`). For edges, Mathlib settles each
of the first two steps by comparing degrees; for cliques each needs a new idea.

We first make "the most `s`-cliques" precise. Mathlib defines `IsTuranMaximal r` as
`IsExtremal (CliqueFree · (r + 1))`, where `IsExtremal p` says that a graph has
property `p` and the most edges among the graphs on its vertex type with property
`p`. To count `s`-cliques instead of edges, we generalize `IsExtremal` from edges to
copies of any graph `H`, counted by `copyCount`. By `copyCount_top` the copies of
`K[s]` are the `s`-cliques, and an edge is a `2`-clique.
-/
/--
`G` is *extremal for copies of `H`* among the graphs with property `p` if it has
property `p` and no graph on the same vertex set with property `p` has more copies
of `H`.
-/
def IsCopyExtremal [Fintype V] {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (p : SimpleGraph V → Prop) : Prop :=
  p G ∧ ∀ ⦃G' : SimpleGraph V⦄, p G' → G'.copyCount H ≤ G.copyCount H

/--
Call `G` *`s`-clique-maximal* for `r` if it is `(r + 1)`-clique-free and no
`(r + 1)`-clique-free graph on the same vertex set has more `s`-cliques. So
`IsNCliqueMaximal 2 r` is equivalent to `IsTuranMaximal r`.
-/
def IsNCliqueMaximal [Fintype V] (G : SimpleGraph V) (s r : ℕ) : Prop :=
  G.IsCopyExtremal K[s] (CliqueFree · (r + 1))

/-!
In the proofs we count `s`-cliques directly, via `cliqueFinset`, using the following
reformulation.
-/
lemma isNCliqueMaximal_iff [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s r : ℕ} : G.IsNCliqueMaximal s r ↔ G.CliqueFree (r + 1) ∧
      ∀ ⦃H : SimpleGraph V⦄ [DecidableRel H.Adj], H.CliqueFree (r + 1) →
        #(H.cliqueFinset s) ≤ #(G.cliqueFinset s) := by
  refine and_congr_right fun _ => ⟨fun h H _ hH => ?_, fun h H hH => ?_⟩
  · simpa only [copyCount_top, Fintype.card_fin] using h hH
  · classical
    simpa only [copyCount_top, Fintype.card_fin] using h hH

/-!
An `s`-clique-maximal graph has at least as many `s`-cliques as any
`(r + 1)`-clique-free graph on the same vertex set.
-/
lemma IsNCliqueMaximal.card_cliqueFinset_le [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] {s r : ℕ} (h : G.IsNCliqueMaximal s r) {H : SimpleGraph V}
  [DecidableRel H.Adj] (hH : H.CliqueFree (r + 1)) :
    #(H.cliqueFinset s) ≤ #(G.cliqueFinset s) :=
  (isNCliqueMaximal_iff.1 h).2 hH

/-!
## Symmetrizing Cliques

Write `dₛ(v)` for the number of `s`-cliques containing `v`. First we need the
analogue of `card_edgeFinset_replaceVertex_of_not_adj` for cliques.

The `s`-cliques of `G.replaceVertex a b` that do not contain `b` are the `s`-cliques
of `G` that do not contain `b`.
-/
lemma isNClique_replaceVertex_iff_of_notMem [DecidableEq V] {a b : V} {s : ℕ}
    {t : Finset V} (hb : b ∉ t) :
    (G.replaceVertex a b).IsNClique s t ↔ G.IsNClique s t := by
  have hadj {x y} (hx : x ∈ t) (hy : y ∈ t) :
      (G.replaceVertex a b).Adj x y ↔ G.Adj x y :=
    adj_replaceVertex_iff_of_ne _ _ (ne_of_mem_of_not_mem hx hb)
      (ne_of_mem_of_not_mem hy hb)
  simp_all [isNClique_iff, isClique_iff, Set.Pairwise]

/-!
The `s`-cliques of `G.replaceVertex a b` containing `b` correspond to the `s`-cliques
of `G` that contain `a` but not `b`.
-/
lemma card_filter_mem_cliqueFinset_replaceVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) (s : ℕ) :
    #{t ∈ (G.replaceVertex a b).cliqueFinset s | b ∈ t} =
      #{t ∈ G.cliqueFinset s | a ∈ t ∧ b ∉ t} := by
  refine card_nbij' (fun t => insert a (t.erase b)) (fun t => insert b (t.erase a))
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) <;>
    simp_rw [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ⊢
  · -- swapping `b` for `a` maps into the target
    have hb : b ∉ insert a (t.erase b) := by simp [hab.symm]
    refine ⟨(isNClique_replaceVertex_iff_of_notMem hb).1
      (ht.1.insert_erase (fun w hw => ?_) ht.2), mem_insert_self _ _, hb⟩
    rw [mem_sdiff, mem_singleton] at hw
    -- in `G.replaceVertex a b`, `a` and `b` have the same neighbours other than `b`
    grind [adj_replaceVertex_iff_of_ne_left, adj_replaceVertex_iff_of_ne_right,
      ht.1.1 ht.2 hw.1 (Ne.symm hw.2)]
  · -- swapping `a` for `b` maps back
    refine ⟨((isNClique_replaceVertex_iff_of_notMem ht.2.2).2 ht.1).insert_erase
      (fun w hw => ?_) ht.2.1, mem_insert_self _ _⟩
    grind [adj_replaceVertex_iff_of_ne_right, ht.1.1 ht.2.1]
  · -- left inverse
    have hat : a ∉ t := fun hat =>
      not_adj_replaceVertex_same G a b (ht.1.1 hat ht.2 hab)
    grind
  · -- right inverse
    grind

/-!
The number of `s`-cliques in `G.replaceVertex a b` expressed in terms of the number
of `s`-cliques in `G` (avoiding `ℕ`-subtraction).
-/
lemma card_cliqueFinset_replaceVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) (s : ℕ) :
    #((G.replaceVertex a b).cliqueFinset s) + #{t ∈ G.cliqueFinset s | b ∈ t} =
      #(G.cliqueFinset s) + #{t ∈ G.cliqueFinset s | a ∈ t ∧ b ∉ t} := by
  have h1 : {t ∈ (G.replaceVertex a b).cliqueFinset s | b ∉ t} =
      {t ∈ G.cliqueFinset s | b ∉ t} := by
    ext t; simpa using and_congr_left isNClique_replaceVertex_iff_of_notMem
  have e1 := card_filter_add_card_filter_not
    (s := (G.replaceVertex a b).cliqueFinset s) (b ∈ ·)
  have e2 := card_filter_add_card_filter_not (s := G.cliqueFinset s) (b ∈ ·)
  grind [card_filter_mem_cliqueFinset_replaceVertex hab]

/-!
If `a` and `b` are not adjacent then no clique contains both, so
`G.replaceVertex a b` loses the `s`-cliques containing `b` and gains one `s`-clique
for each `s`-clique containing `a`.
-/
lemma card_cliqueFinset_replaceVertex_of_not_adj [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a b : V} (hn : ¬G.Adj a b) (s : ℕ) :
    #((G.replaceVertex a b).cliqueFinset s) + #{t ∈ G.cliqueFinset s | b ∈ t} =
      #(G.cliqueFinset s) + #{t ∈ G.cliqueFinset s | a ∈ t} := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  rw [card_cliqueFinset_replaceVertex hab]
  congr 2
  refine filter_congr fun t ht => ⟨fun h => h.1, fun hat => ⟨hat, fun hbt => ?_⟩⟩
  exact hn ((mem_cliqueFinset_iff.1 ht).1 hat hbt hab)

/-!
As in Mathlib's proof of Turán's theorem, performing Zykov symmetrization on a pair
of non-adjacent vertices in an `s`-clique-maximal graph shows that they lie in the
same number of `s`-cliques.
-/
lemma IsNCliqueMaximal.card_filter_mem_eq_of_not_adj [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {s r : ℕ} (h : G.IsNCliqueMaximal s r)
    {a b : V} (hn : ¬G.Adj a b) :
    #{t ∈ G.cliqueFinset s | a ∈ t} = #{t ∈ G.cliqueFinset s | b ∈ t} := by
  have kab := card_cliqueFinset_replaceVertex_of_not_adj hn s
  have kba := card_cliqueFinset_replaceVertex_of_not_adj (fun h' => hn h'.symm) s
  have := h.card_cliqueFinset_le (h.1.replaceVertex a b)
  have := h.card_cliqueFinset_le (h.1.replaceVertex b a)
  grind

/-!
## Complete Multipartite Maximizers

Now comes the first real difference from the proof for edges (Turán's theorem).
Suppose that `u` and `w` are adjacent, while `v` is adjacent to neither. Mathlib
calls this `IsPathGraph3Compl`, since `u`, `v` and `w` induce the complement of a
path on three vertices, and a graph is complete multipartite exactly when it contains
no such triple (`not_isCompleteMultipartite_iff_exists_isPathGraph3Compl`).

[Figure: Left: $P_3$. Right: its complement.](https://jt496.github.io/GraphTheoryInLean/figures/path3_compl.svg)

Symmetrizing twice, replacing `u` and `w` by copies of `v`, changes the number of
`s`-cliques by `dₛ(v) - dₛ(u) + dₛ(v) - dₛ(w) + dₛ(u, w)`, where `dₛ(u, w)` counts
the `s`-cliques containing both `u` and `w`
(`card_cliqueFinset_replaceVertex_replaceVertex` below). Maximality then forces
`dₛ(u) = dₛ(v) = dₛ(w)` (`IsNCliqueMaximal.card_filter_mem_eq_of_not_adj`), but
`dₛ(u, w)` can be `0`, so there is no contradiction. Indeed an `s`-clique-maximal
graph need not be complete multipartite: for `s > r` every `(r + 1)`-clique-free
graph has no `s`-cliques, so every one of them is `s`-clique-maximal. (For edges,
`s = 2` and `dₛ(u, w) = 1`, so any `2`-clique-maximal graph is complete multipartite,
by `IsTuranMaximal.not_adj_trans`.)

The number of `s`-cliques in `(G.replaceVertex v u).replaceVertex v w` in terms of
the number of `s`-cliques in `G`, when the only edge induced by `{u, v, w}` is
`u — w`.
-/
lemma card_cliqueFinset_replaceVertex_replaceVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v w : V} (h : G.IsPathGraph3Compl v u w) (s : ℕ) :
    #(((G.replaceVertex v u).replaceVertex v w).cliqueFinset s) +
        #{t ∈ G.cliqueFinset s | u ∈ t} + #{t ∈ G.cliqueFinset s | w ∈ t} =
      #(G.cliqueFinset s) + 2 * #{t ∈ G.cliqueFinset s | v ∈ t} +
        #{t ∈ G.cliqueFinset s | u ∈ t ∧ w ∈ t} := by
  have nvu : v ≠ u := h.ne_fst
  have nuw : u ≠ w := h.fst_ne_snd
  obtain ⟨huw, hvu, hvw⟩ := h
  have hn₁ : ¬(G.replaceVertex v u).Adj v w :=
    (G.adj_replaceVertex_iff_of_ne v nvu nuw.symm).not.mpr hvw
  have hv : {t ∈ (G.replaceVertex v u).cliqueFinset s | v ∈ t} =
      {t ∈ G.cliqueFinset s | v ∈ t} := by
    ext t
    simp only [mem_filter, mem_cliqueFinset_iff, and_congr_left_iff]
    intro hvt
    by_cases hut : u ∈ t
    · exact iff_of_false
        (fun ht => G.not_adj_replaceVertex_same v u (ht.1 hvt hut nvu))
        fun ht => hvu (ht.1 hvt hut nvu)
    · exact isNClique_replaceVertex_iff_of_notMem hut
  have hw : {t ∈ (G.replaceVertex v u).cliqueFinset s | w ∈ t} =
      {t ∈ G.cliqueFinset s | w ∈ t ∧ u ∉ t} := by
    ext t
    simp only [mem_filter, mem_cliqueFinset_iff]
    constructor
    · rintro ⟨ht, hwt⟩
      have hut : u ∉ t := fun hut => hvw <|
        (adj_replaceVertex_iff_of_ne_right G v nuw.symm).1 (ht.1 hut hwt nuw)
      exact ⟨(isNClique_replaceVertex_iff_of_notMem hut).1 ht, hwt, hut⟩
    · rintro ⟨ht, hwt, hut⟩
      exact ⟨(isNClique_replaceVertex_iff_of_notMem hut).2 ht, hwt⟩
  have huw' : #{t ∈ G.cliqueFinset s | u ∈ t ∧ w ∈ t} +
      #{t ∈ G.cliqueFinset s | w ∈ t ∧ u ∉ t} = #{t ∈ G.cliqueFinset s | w ∈ t} := by
    rw [← card_filter_add_card_filter_not (s := {t ∈ G.cliqueFinset s | w ∈ t})
      (u ∈ ·), filter_filter, filter_filter]
    simp_rw [and_comm]
  have k₁ := card_cliqueFinset_replaceVertex_of_not_adj hvu s
  have k₂ := card_cliqueFinset_replaceVertex_of_not_adj hn₁ s
  grind

/-!
The problem is caused by edges that lie in no `s`-clique. Deleting all such edges
does not change the number of `s`-cliques, and will yield a subgraph that we *can*
prove is complete multipartite.

We do this by forming the graph `G.cliqueUnion s`, which is the union of all the
`s`-cliques of `G`.
-/
/-- The union of the `s`-cliques of `G`: distinct vertices are adjacent iff they lie
in a common `s`-clique of `G`. -/
@[simps]
def cliqueUnion (G : SimpleGraph V) (s : ℕ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ t, G.IsNClique s t ∧ x ∈ t ∧ y ∈ t

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s : ℕ} :
    DecidableRel (G.cliqueUnion s).Adj := fun x y =>
  decidable_of_iff (x ≠ y ∧ ∃ t ∈ G.cliqueFinset s, x ∈ t ∧ y ∈ t) (by simp)

/-!
The union of the `s`-cliques of `G` is a subgraph of `G`.
-/
lemma cliqueUnion_le (s : ℕ) : G.cliqueUnion s ≤ G :=
  fun _ _ ⟨hxy, _, ht, hx, hy⟩ => ht.1 hx hy hxy

/-!
The `s`-cliques of `G.cliqueUnion s` are the same as those of `G`.
-/
@[simp]
lemma isNClique_cliqueUnion_iff {s : ℕ} {t : Finset V} :
    (G.cliqueUnion s).IsNClique s t ↔ G.IsNClique s t :=
  ⟨fun ht => ht.mono (G.cliqueUnion_le s),
    fun ht => ⟨fun _ hx _ hy hxy => ⟨hxy, t, ht, hx, hy⟩, ht.2⟩⟩

/-!
The finite set of `s`-cliques of `G.cliqueUnion s` is the same as the finite set of
`s`-cliques of `G`.
-/
@[simp]
lemma cliqueFinset_cliqueUnion [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (s : ℕ) : (G.cliqueUnion s).cliqueFinset s = G.cliqueFinset s := by
  ext t; simp

/-!
Every edge of `G.cliqueUnion s` lies in an `s`-clique of `G.cliqueUnion s`.
-/
lemma cliqueUnion_cliqueUnion (s : ℕ) :
    (G.cliqueUnion s).cliqueUnion s = G.cliqueUnion s := by
  ext; simp

/-!
Our next lemma looks a little odd mathematically. The hypothesis
`G ≤ G.cliqueUnion s` should be read as "every edge of `G` lies in an `s`-clique".
(Obviously we also have `G.cliqueUnion s ≤ G` so in fact `G = G.cliqueUnion s`.)

If `G` is `s`-clique-maximal and every edge of `G` lies in an `s`-clique, then `G` is
complete multipartite.
-/
lemma IsNCliqueMaximal.isCompleteMultipartite_of_le_cliqueUnion [Fintype V]
    {s r : ℕ} (h : G.IsNCliqueMaximal s r)
    (hG : G ≤ G.cliqueUnion s) : G.IsCompleteMultipartite := by
  classical
  by_contra hcm
  obtain ⟨v, u, w, h3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hcm
  have hk := card_cliqueFinset_replaceVertex_replaceVertex h3 s
  have := h.card_filter_mem_eq_of_not_adj h3.not_adj_fst
  have := h.card_filter_mem_eq_of_not_adj h3.not_adj_snd
  have := h.card_cliqueFinset_le ((h.1.replaceVertex v u).replaceVertex v w)
  -- the edge `u — w` lies in an `s`-clique
  obtain ⟨-, t, ht, hut, hwt⟩ := hG h3.adj
  have : 0 < #{t ∈ G.cliqueFinset s | u ∈ t ∧ w ∈ t} :=
    card_pos.2 ⟨t, by simp [ht, hut, hwt]⟩
  grind

/-!
The next key observation is that a complete multipartite graph with one `s`-clique
has many. Let `t` be an `s`-clique and let `x` and `y` be adjacent. At most one
vertex of `t` is not adjacent to `x`, since two such vertices would both lie in the
part of `x`, and similarly for `y`. So at least `s - 2` vertices of `t` are adjacent
to both `x` and `y`, and together with `x` and `y` they form an `s`-clique. We allow
the edge `x — y` to come from a larger graph `H`, so that `x` and `y` may lie in the
same part of `G`, as on the right of the figure below. We need this twice: in
`IsNCliqueMaximal.isCompleteMultipartite`, where `G.cliqueUnion s` plays the role of
`G` and `G` plays the role of `H`, and in
`IsNCliqueMaximal.not_cliqueFree_of_not_adj`, where `H` is `G` with an edge added
inside a part.

[Figure: A complete multipartite graph with four parts and a $4$-clique $t$ (blue). Left: if $x$ and $y$ lie in different parts, the vertices of $t$ outside the parts of $x$ and $y$ form a $4$-clique with $x$ and $y$ (orange). Right: if $x$ and $y$ lie in the same part and the edge between them (dashed) is added, any two vertices of $t$ outside that part form a $4$-clique with $x$ and $y$.](https://jt496.github.io/GraphTheoryInLean/figures/clique_through_edge.svg)

If `G` is complete multipartite and has an `s`-clique, then every edge of a graph
`H` containing `G` lies in an `s`-clique of `H`.
-/
lemma IsCompleteMultipartite.exists_isNClique_of_le (hc : G.IsCompleteMultipartite)
    {H : SimpleGraph V} (hGH : G ≤ H) {s : ℕ} (hs : 2 ≤ s) {t : Finset V}
    (ht : G.IsNClique s t) {x y : V} (hxy : H.Adj x y) :
    ∃ t', H.IsNClique s t' ∧ x ∈ t' ∧ y ∈ t' := by
  classical
  -- at most one vertex of `t` is not adjacent to a given vertex `z`
  have hle (z : V) : #{a ∈ t | ¬G.Adj z a} ≤ 1 := by
    refine card_le_one.2 fun a ha b hb => ?_
    rw [mem_filter] at ha hb
    by_contra hab
    exact hc.trans _ _ _ (fun h => ha.2 h.symm) hb.2 (ht.1 ha.1 hb.1 hab)
  have hcard : s - 2 ≤ #{a ∈ t | G.Adj x a ∧ G.Adj y a} := by
    have := card_filter_add_card_filter_not (s := t) fun a => G.Adj x a ∧ G.Adj y a
    simp only [not_and_or, filter_or] at this
    have := card_union_le {a ∈ t | ¬G.Adj x a} {a ∈ t | ¬G.Adj y a}
    grind [hle x, hle y, ht.2]
  obtain ⟨t₀, ht₀, ht₀2⟩ := exists_subset_card_eq hcard
  have hxyt₀ (a) (ha : a ∈ t₀) : G.Adj x a ∧ G.Adj y a := (mem_filter.1 (ht₀ ha)).2
  have ht₀' : H.IsNClique (s - 2) t₀ :=
    ⟨(ht.1.subset (coe_subset.2 (ht₀.trans (filter_subset _ _)))).mono hGH, ht₀2⟩
  have hyt₀ := ht₀'.insert fun b hb => hGH (hxyt₀ b hb).2
  have hxt₀ := hyt₀.insert ((forall_mem_insert _ _ _).2
    ⟨hxy, fun b hb => hGH (hxyt₀ b hb).1⟩)
  exact ⟨_, Nat.sub_add_cancel hs ▸ hxt₀, mem_insert_self _ _,
    mem_insert_of_mem (mem_insert_self _ _)⟩

/-!
Now let `G` be `s`-clique-maximal with at least one `s`-clique. Then
`G.cliqueUnion s` is `s`-clique-maximal too, and every edge of it lies in an
`s`-clique, so it is complete multipartite. Applying the previous lemma to it, with
`H = G`, shows that every edge of `G` lies in an `s`-clique, so `G` is complete
multipartite as well.
-/
lemma IsNCliqueMaximal.isCompleteMultipartite [Fintype V] {s r : ℕ}
    (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s)
    {t : Finset V} (ht : G.IsNClique s t) : G.IsCompleteMultipartite := by
  classical
  have h₀ : (G.cliqueUnion s).IsNCliqueMaximal s r :=
    ⟨h.1.anti (G.cliqueUnion_le s), fun H hH => by
      simpa [copyCount_top] using h.2 hH⟩
  have hc₀ :=
    h₀.isCompleteMultipartite_of_le_cliqueUnion (cliqueUnion_cliqueUnion s).ge
  refine h.isCompleteMultipartite_of_le_cliqueUnion fun x y hxy => ?_
  obtain ⟨t', ht', hx, hy⟩ := hc₀.exists_isNClique_of_le (G.cliqueUnion_le s) hs
    (isNClique_cliqueUnion_iff.2 ht) hxy
  exact ⟨hxy.ne, t', ht', hx, hy⟩

/-!
## Balancing the Parts

The Turán graph `T[n, r]` is not just complete multipartite, it is also
balanced. For general `s`-cliques this "balancing of parts" argument is again more
involved.

Suppose that `G` is an unbalanced complete multipartite graph. Let `A` and `B` be
parts with `#B + 1 < #A`, and move a vertex `w` from `A` to `B` while keeping the
graph complete multipartite: this is `G.replaceVertex v w` for any `v` in `B`. The
number of `s`-cliques changes by `#A - #B - 1` times the number of `(s - 2)`-cliques
in the other parts. To contradict maximality we need this change to be positive, and
it is as long as `G` has an `s`-clique.

[Figure: Moving $w$ from the part $A$ to the part $B$ of $v$ turns $G$ (left) into `G.replaceVertex v w` (right). The triangles containing $w$ and a vertex $c$ of another part $C$ change from one for each vertex of $B$ to one for each vertex of $A$ other than $w$, in this case from $3$ to $4$.](https://jt496.github.io/GraphTheoryInLean/figures/zykov_move.svg)

The figure above shows why moving `w` works, but the proof does not compute these
numbers directly. Instead it compares the cliques that the move destroys with those
that it creates. By `card_cliqueFinset_replaceVertex`, the move destroys the
`s`-cliques containing `w` and creates one for each `s`-clique of `G` that contains
`v` but not `w`, since `w` takes over the neighbours of `v`. So it is enough to map
the first set injectively into the second, missing at least one clique.

Since the parts are unbalanced, `A` has at least `#B + 2` vertices, so we can choose
a vertex `a` in `A \ {w}`. We first build the map that will transfer the cliques. Map
`B` injectively into `A \ {w, a}` using some `φ`, and extend `φ` to a map `σ : V → V`
that sends `w` to `v`, and fixes every other vertex.

Every `s`-clique containing `w` lies in its closed neighbourhood
`insert w (G.neighborSet w)`, which consists of `w` and the vertices outside `A`. On
these vertices `σ` sends `w` into `B`, sends `B` into `A`, and fixes the rest. As `w`
is the only vertex of `A` in this neighbourhood, `σ` sends vertices in different
parts to vertices in different parts, so it preserves adjacency there. It is also
injective there, and never takes the value `w` or `a`.

[Figure: Left: the map $\sigma$ sends $w$ to $v$, maps $B$ injectively into $A \setminus \{w, a\}$, and fixes every other vertex. Right: $\sigma$ pairs each triangle that the move destroys (blue) with a triangle containing $v$ but not $w$ (orange); the move creates a copy of it with $w$ in place of $v$. No triangle is paired with the magenta one containing $a$, so the move creates more triangles than it destroys.](https://jt496.github.io/GraphTheoryInLean/figures/zykov_transfer.svg)

Let `G` be complete multipartite, let the part of `w` have at least two more
vertices than the part of `v`, and let `a ≠ w` lie in the part of `w`. Then some map
sends `w` to `v`, and is injective and preserves adjacency on the closed
neighbourhood of `w`, where it avoids `w` and `a`.
-/
lemma IsCompleteMultipartite.exists_transfer [Fintype V] [DecidableRel G.Adj]
    (hc : G.IsCompleteMultipartite) {v w a : V} (hvw : G.Adj v w)
    (hwa : ¬G.Adj w a) (haw : a ≠ w)
    (hlt : #{x | ¬G.Adj v x} + 1 < #{x | ¬G.Adj w x}) :
    ∃ σ : V → V, Set.InjOn σ (insert w (G.neighborSet w)) ∧
      (∀ ⦃x⦄, x ∈ insert w (G.neighborSet w) → ∀ ⦃y⦄,
        y ∈ insert w (G.neighborSet w) → G.Adj x y → G.Adj (σ x) (σ y)) ∧
      σ w = v ∧ ∀ x ∈ insert w (G.neighborSet w), σ x ≠ w ∧ σ x ≠ a := by
  classical
  set A : Finset V := {x | ¬G.Adj w x}
  set B : Finset V := {x | ¬G.Adj v x}
  have nt {x y z : V} (h₁ : ¬G.Adj x y) (h₂ : ¬G.Adj y z) : ¬G.Adj x z :=
    hc.trans _ _ _ h₁ h₂
  have hwA : w ∈ A := by simp [A]
  have haA : a ∈ A := by simp [A, hwa]
  -- every vertex of `A` is adjacent to every vertex of `B`
  have hAB {x y : V} (hx : x ∈ A) (hy : y ∈ B) : G.Adj x y := by grind [Adj.symm]
  -- an injection `φ` from `B` to `A \ {w, a}`
  have hcard : Fintype.card B ≤ Fintype.card ((A.erase w).erase a) := by
    simp only [Fintype.card_coe, card_erase_of_mem (mem_erase.2 ⟨haw, haA⟩),
      card_erase_of_mem hwA]
    grind
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  let σ : V → V := fun x => if x = w then v else if hx : x ∈ B then φ ⟨x, hx⟩ else x
  refine ⟨σ, fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_, by simp [σ],
    fun x hx => ?_⟩ <;>
      grind [mem_neighborSet, φ.injective.eq_iff, Subtype.ext_iff, Adj.symm]

/-!
Now let `t` be an `s`-clique containing `w`. It lies in the closed neighbourhood of
`w`, so `t.image σ` is again an `s`-clique, by `IsNClique.image_of_adj` from
[Cliques](#chapter-cliques). It contains `v` but neither `w` nor `a`.
Different cliques have different images, since `σ` is injective on the whole closed
neighbourhood and not just on each clique. So `t ↦ t.image σ` is an injection from
the `s`-cliques containing `w` to those containing `v` that avoid `w` and `a`: this
is the inequality below. Avoiding `a` is exactly what we need in
`IsNCliqueMaximal.card_le_card_add_one`, where we find an `s`-clique containing `v`
and `a` but not `w`. It contains `a`, so the injection misses it and the change is
strictly positive.
-/
lemma IsCompleteMultipartite.card_filter_mem_cliqueFinset_le [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hc : G.IsCompleteMultipartite) {v w a : V}
    (hvw : G.Adj v w) (hwa : ¬G.Adj w a) (haw : a ≠ w)
    (hlt : #{x | ¬G.Adj v x} + 1 < #{x | ¬G.Adj w x}) (s : ℕ) :
    #{t ∈ G.cliqueFinset s | w ∈ t} ≤
      #{t ∈ G.cliqueFinset s | v ∈ t ∧ w ∉ t ∧ a ∉ t} := by
  obtain ⟨σ, hinj, hadj, hσw, hσ⟩ := hc.exists_transfer hvw hwa haw hlt
  -- the cliques containing `w` lie in its closed neighbourhood
  have hsub {t : Finset V} (ht : G.IsNClique s t) (hwt : w ∈ t) :
      (t : Set V) ⊆ insert w (G.neighborSet w) := fun x hx =>
    (eq_or_ne x w).imp_right fun hxw => ht.1 hwt hx hxw.symm
  refine card_le_card_of_injOn (fun t => t.image σ) (fun t ht => ?_)
    (fun t ht t' ht' htt' => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ⊢
    obtain ⟨ht, hwt⟩ := ht
    refine ⟨ht.image_of_adj fun x hx y hy => hadj (hsub ht hwt hx) (hsub ht hwt hy),
      mem_image.2 ⟨w, hwt, hσw⟩, fun hw => ?_, fun ha => ?_⟩
    · obtain ⟨x, hx, hxw⟩ := mem_image.1 hw
      exact (hσ x (hsub ht hwt hx)).1 hxw
    · obtain ⟨x, hx, hxa⟩ := mem_image.1 ha
      exact (hσ x (hsub ht hwt hx)).2 hxa
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ht' htt'
    apply Finset.coe_injective
    exact (hinj.image_eq_image_iff
      (hsub ht.1 ht.2) (hsub ht'.1 ht'.2)).1
        (by exact_mod_cast htt')

/-!
An `s`-clique-maximal graph with at least one `s`-clique has balanced parts: any two
vertices have numbers of non-neighbours that differ by at most one, and the
non-neighbours of a vertex form its part
(`IsCompleteMultipartite.part_finpartition`).
-/
lemma IsNCliqueMaximal.card_le_card_add_one [Fintype V] [DecidableRel G.Adj]
    {s r : ℕ} (h : G.IsNCliqueMaximal s r)
    (hs : 2 ≤ s) {t : Finset V} (ht : G.IsNClique s t) (v w : V) :
    #{x | ¬G.Adj w x} ≤ #{x | ¬G.Adj v x} + 1 := by
  classical
  by_contra! hlt
  have hc := h.isCompleteMultipartite hs ht
  have hvw := hc.adj_of_card_ne (v := v) (w := w) (by grind)
  obtain ⟨a, ha, haw⟩ := exists_mem_ne (s := {x | ¬G.Adj w x}) (by grind) w
  have hwa : ¬G.Adj w a := (mem_filter.1 ha).2
  -- some `s`-clique contains `v` and `a`, and hence not `w`
  have hva : G.Adj v a := by grind [hc.trans, Adj.symm]
  obtain ⟨t', ht', hvt', hat'⟩ := hc.exists_isNClique_of_le le_rfl hs ht hva
  have hwt' : w ∉ t' := fun hwt' => hwa (ht'.1 hwt' hat' haw.symm)
  have hd := hc.card_filter_mem_cliqueFinset_le hvw hwa haw hlt s
  have hd' : #{t ∈ G.cliqueFinset s | v ∈ t ∧ w ∉ t ∧ a ∉ t} <
      #{t ∈ G.cliqueFinset s | v ∈ t ∧ w ∉ t} :=
    card_lt_card <| (ssubset_iff_of_subset
      (monotone_filter_right _ fun _ _ ht => ⟨ht.1, ht.2.1⟩)).2
        ⟨t', by simp [ht', hvt', hwt'], by simp [hat']⟩
  have hk := card_cliqueFinset_replaceVertex (G := G) hvw.ne s
  have := h.card_cliqueFinset_le (h.1.replaceVertex v w)
  grind

/-!
Any `s`-clique-maximal graph with at least one `s`-clique is either complete or
contains an `r`-clique.
-/
lemma IsNCliqueMaximal.not_cliqueFree_of_not_adj [Fintype V] {s r : ℕ}
    (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s) {t : Finset V}
    (ht : G.IsNClique s t) {x y : V} (hxy : x ≠ y) (hn : ¬G.Adj x y) :
    ¬G.CliqueFree r := by
  intro hcf
  classical
  have hxy' : (G ⊔ edge x y).Adj x y := by simp [edge_adj, hxy]
  obtain ⟨t', ht', hxt', hyt'⟩ :=
    (h.isCompleteMultipartite hs ht).exists_isNClique_of_le le_sup_left hs ht hxy'
  have hlt : G.cliqueFinset s ⊂ (G ⊔ edge x y).cliqueFinset s :=
    (ssubset_iff_of_subset (cliqueFinset_mono _ le_sup_left)).2
      ⟨t', mem_cliqueFinset_iff.2 ht',
        fun hG => hn ((mem_cliqueFinset_iff.1 hG).1 hxt' hyt' hxy)⟩
  exact (card_lt_card hlt).not_ge (h.card_cliqueFinset_le (hcf.sup_edge x y))

/-!
## The Bound and the Extremal Graphs

We have shown that, for `2 ≤ s`, an `s`-clique-maximal graph with an `s`-clique is
complete multipartite, that its parts are balanced, and that it has an `r`-clique
unless it is complete. So it is a Turán graph, by
`IsCompleteMultipartite.nonempty_iso_turanGraph`
([Proof of Turán's Theorem](#section-proof-of-tur-n-s-theorem)).
-/
theorem IsNCliqueMaximal.nonempty_iso_turanGraph [Fintype V] {s r : ℕ}
    (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s)
    {t : Finset V} (ht : G.IsNClique s t) :
    Nonempty (G ≃g T[Fintype.card V, r]) := by
  classical
  exact (h.isCompleteMultipartite hs ht).nonempty_iso_turanGraph h.1
    (h.card_le_card_add_one hs ht) fun _ _ => h.not_cliqueFree_of_not_adj hs ht

/-!
Two small facts remain to prove.

For `s ≤ 1` every set of `s` vertices is a clique, so the `s`-cliques do not depend
on the graph.
-/
lemma cliqueFinset_eq_of_le_one [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {H : SimpleGraph V} [DecidableRel H.Adj] {s : ℕ} (hs : s ≤ 1) :
    G.cliqueFinset s = H.cliqueFinset s := by
  -- `interval_cases s` splits into one case for each value of `s` allowed by the
  -- bounds (here `0` and `1`)
  interval_cases s <;> ext <;> simp [isNClique_zero, isNClique_one]

/-!
Isomorphic graphs have the same number of `s`-cliques.
-/
lemma Iso.card_cliqueFinset_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (e : G ≃g H) (s : ℕ) : #(G.cliqueFinset s) = #(H.cliqueFinset s) := by
  -- the `s`-cliques are the copies of `K[s]` (`copyCount_top`)
  have h := Iso.copyCount_eq (.refl : K[s] ≃g K[s]) e
  rwa [copyCount_top, copyCount_top, Fintype.card_fin] at h

/-!
Zykov's theorem follows. Let `G` be `(r + 1)`-clique-free. The `(r + 1)`-clique-free
graphs on `V` form a finite set, which contains `G` and so is nonempty. A graph `H`
in it with the most `s`-cliques is `s`-clique-maximal, and `G` has at most as many
`s`-cliques as `H`. If `H` has no `s`-clique then neither does `G`, so the bound
holds trivially. If `H` has an `s`-clique and `2 ≤ s`, then `H` is a Turán graph,
which gives the bound. For `s ≤ 1` we instead compare both graphs with an empty
graph, using `cliqueFinset_eq_of_le_one`.
-/
/-- **Zykov's theorem**: an `(r + 1)`-clique-free graph on `n` vertices has at most
as many `s`-cliques as the Turán graph `T[n, r]`. -/
theorem CliqueFree.card_cliqueFinset_le [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1)) (s : ℕ) :
    #(G.cliqueFinset s) ≤ #(T[Fintype.card V, r].cliqueFinset s) := by
  rcases lt_or_ge s 2 with hs | hs
  · -- for `s ≤ 1` compare the empty graphs on `V` and `Fin (card V)`
    let e := Iso.emptyGraph (Fintype.equivFin V)
    rw [cliqueFinset_eq_of_le_one (H := ⊥) (by grind),
      cliqueFinset_eq_of_le_one (G := T[_, r]) (H := ⊥) (by grind)]
    exact (e.card_cliqueFinset_eq s).le
  classical
  -- `G` is `(r + 1)`-clique-free, so a graph `H` with the most `s`-cliques exists
  obtain ⟨H, hH, hmax⟩ :=
    ({H | H.CliqueFree (r + 1)} : Finset (SimpleGraph V)).exists_max_image
      (·.copyCount K[s]) ⟨G, by simpa using h⟩
  have hH' : H.IsNCliqueMaximal s r :=
    ⟨by simpa using hH, fun H' hH' => hmax H' (by simpa using hH')⟩
  have hGH := hH'.card_cliqueFinset_le h
  rcases (H.cliqueFinset s).eq_empty_or_nonempty with he | ⟨t, ht⟩
  · grind
  · obtain ⟨e⟩ := hH'.nonempty_iso_turanGraph hs (mem_cliqueFinset_iff.1 ht)
    exact hGH.trans (e.card_cliqueFinset_eq s).le

/-!
So a `4`-clique-free graph on `7` vertices has at most `12` triangles.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hV : Fintype.card V = 7)
    (h : G.CliqueFree 4) : #(G.cliqueFinset 3) ≤ 12 :=
  (h.card_cliqueFinset_le (r := 3) 3).trans_eq (by rw [hV]; decide)

/-!
Turán's theorem also says that the Turán graph is the *only* extremal graph
(`isTuranMaximal_iff_nonempty_iso_turanGraph`). The same is true for Zykov's theorem
when `2 ≤ s ≤ r` and `s ≤ n`. The other cases are degenerate, since all
`(r + 1)`-clique-free graphs on `n` vertices then have the same number of
`s`-cliques: `1` if `s = 0`, `n` if `s = 1`, and `0` if `s > r` or `s > n`.

When `s ≤ r` and `s ≤ n`, the vertices `0, …, s - 1` of the Turán graph lie in
different parts, so it has an `s`-clique. A graph with as many `s`-cliques as the
Turán graph is `s`-clique-maximal, since by the bound just proved
(`CliqueFree.card_cliqueFinset_le`) no `(r + 1)`-clique-free graph has more. So it
has an `s`-clique too, and it is a Turán graph by
`IsNCliqueMaximal.nonempty_iso_turanGraph`.
-/
/-- **Zykov's theorem**, equality case: for `2 ≤ s ≤ r` and `s ≤ n`, an
`(r + 1)`-clique-free graph on `n` vertices has as many `s`-cliques as `T[n, r]` iff
it is isomorphic to `T[n, r]`. -/
theorem CliqueFree.card_cliqueFinset_eq_iff_nonempty_iso_turanGraph [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r s : ℕ} (h : G.CliqueFree (r + 1))
    (hs : 2 ≤ s) (hsr : s ≤ r) (hsn : s ≤ Fintype.card V) :
    #(G.cliqueFinset s) = #(T[Fintype.card V, r].cliqueFinset s) ↔
      Nonempty (G ≃g T[Fintype.card V, r]) := by
  refine ⟨fun hk => ?_, fun ⟨e⟩ => e.card_cliqueFinset_eq s⟩
  have hT : T[Fintype.card V, r].IsNClique s
      (univ.map (Fin.castLEEmb hsn)) := by
    refine ⟨?_, by simp⟩
    simp only [coe_map, coe_univ, Set.image_univ]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    simpa [turanGraph_adj, Nat.mod_eq_of_lt (i.isLt.trans_le hsr),
      Nat.mod_eq_of_lt (j.isLt.trans_le hsr), Fin.val_inj] using hij
  obtain ⟨t, ht⟩ : (G.cliqueFinset s).Nonempty := by
    rw [← card_pos, hk]
    exact card_pos.2 ⟨_, mem_cliqueFinset_iff.2 hT⟩
  exact IsNCliqueMaximal.nonempty_iso_turanGraph (isNCliqueMaximal_iff.2
    ⟨h, fun H _ hH => (hH.card_cliqueFinset_le s).trans hk.ge⟩) hs
    (mem_cliqueFinset_iff.1 ht)

/-!
So among `(r + 1)`-clique-free graphs on `n` vertices, one with the most `s`-cliques,
for any `2 ≤ s ≤ min r n`, also has the most edges. For example, a `4`-clique-free
graph with as many triangles as `T[n, 3]` has `turanNumber n 3` edges.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {r s : ℕ}
    (h : G.CliqueFree (r + 1)) (hs : 2 ≤ s) (hsr : s ≤ r) (hsn : s ≤ Fintype.card V)
    (hk : #(G.cliqueFinset s) = #(T[Fintype.card V, r].cliqueFinset s)) :
    #G.edgeFinset = turanNumber (Fintype.card V) r := by
  obtain ⟨e⟩ := (h.card_cliqueFinset_eq_iff_nonempty_iso_turanGraph hs hsr hsn).1 hk
  exact e.card_edgeFinset_eq

/-!
For `s = 2` the `s`-cliques are just the edges, so Zykov's theorem contains Turán's
theorem, including the uniqueness of the extremal graph (Exercises 16–18). Our proof
of Zykov's theorem does not use Turán's theorem, so this gives a second proof of it.

# Regularity and Removal *

The Szemerédi regularity lemma (`szemeredi_regularity`) is one of the most important
tools in modern extremal combinatorics. Mathlib has it together with two classic
applications: the triangle removal lemma (`triangle_removal`) and a graph-theoretic
proof of Roth's theorem on three-term arithmetic progressions
(`roth_3ap_theorem_nat`). We end with a third application, which is not quite in
Mathlib but follows very easily: the Ruzsa–Szemerédi theorem
(`ruzsaSzemerediNumberNat_isLittleO`).

## Edge Density and Uniform Pairs

The *edge density* between two finite sets `s` and `t` of vertices is the fraction of
pairs in `s ×ˢ t` that are edges. It is a rational number, so we can compute it.
-/
#check edgeDensity_def -- G.edgeDensity s t = #(G.interedges s t) / (#s * #t)
#eval C[6].edgeDensity {0, 2, 4} {1, 3, 5} -- 2 / 3
#eval K[6].edgeDensity {0, 2, 4} {1, 3, 5} -- 1

/-!
A pair `(s, t)` is `ε`-*uniform* if the edges between them are spread evenly: any
`s' ⊆ s` and `t' ⊆ t` containing at least an `ε` fraction of `s` and `t` have edge
density within `ε` of the density between `s` and `t`. This mimics a random
bipartite subgraph.
-/
#source IsUniform

/-!
## The Szemerédi Regularity Lemma

The *regularity lemma*
[Szemerédi 1978](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-szemeredi-1978)
says that for every `ε > 0`, every finite graph can be approximated by a structured
one: its vertices can be partitioned into a bounded number of almost equal parts so
that most pairs of parts are `ε`-uniform.

[Figure: An $\varepsilon$-uniform partition; the band between two parts is shaded by their edge density](https://jt496.github.io/GraphTheoryInLean/figures/szemeredi.svg)

In Mathlib's statement, `Finpartition.IsEquipartition` says the parts of a
`Finpartition` differ in size by at most `1`, and `Finpartition.IsUniform` says that
at most an `ε` fraction of the pairs of parts are not `ε`-uniform. Given
`l ≤ Fintype.card V`, the number of parts is between `l` and `bound ε l`. Crucially,
this bound depends only on `ε` and `l`, not on the graph.
-/
#source Finpartition
#check szemeredi_regularity

/-!
## The Triangle Removal Lemma

If `H` has an edge (`H ≠ ⊥`), any graph can be made `H`-free by deleting one edge
from each copy of `H`. Mathlib calls the resulting graph `killCopies`, and it has
lost no more than `G.copyCount H` edges, one for each copy of `H` in `G` (see
`copyCount`).
-/
#check free_killCopies -- H ≠ ⊥ → H.Free (G.killCopies H)
#check le_card_edgeFinset_killCopies

/-!
The triangle removal lemma
[Ruzsa–Szemerédi 1978](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-ruzsa-szemeredi-1978)
is a far stronger statement: for every `ε > 0`, there is `δ > 0`, independent of `n`,
such that any graph on `n` vertices with fewer than `δ * n³` triangles can be made
triangle-free by deleting fewer than `ε * n²` edges. Thus `o(n³)` triangles can be
eliminated by deleting `o(n²)` edges. In Mathlib a graph is
`ε`-*far from triangle-free* if at least `ε * n²` edges must be deleted to make it
triangle-free.
-/
#source FarFromTriangleFree

/-!
The lemma is proved by applying the regularity lemma, and then a *counting lemma*:
three parts that are pairwise uniform and dense span many triangles.
-/
#check triangle_counting
#check FarFromTriangleFree.le_card_cliqueFinset
#check triangle_removal

/-!
## Roth's Theorem

The triangle removal lemma has a striking application in additive number theory.

*Roth's theorem*
[Roth 1953](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-roth-1953)
says that a set of integers with positive density contains a three-term arithmetic
progression `a, a + d, a + 2 * d` with `d ≠ 0`. More precisely, for every `ε > 0` and
all large enough `n`, every subset of `{0, …, n - 1}` with at least `ε * n` elements
contains one. Mathlib phrases this as `¬ThreeAPFree`.
-/
#check roth_3ap_theorem_nat

/-!
The proof goes via the *corners theorem*: a dense set of points in the grid contains
a corner `(x, y), (x + d, y), (x, y + d)` with `d ≠ 0`.
-/
#check corners_theorem_nat

/-!
## The Ruzsa–Szemerédi Theorem

A graph is *locally linear* (`LocallyLinear`) if every edge lies in exactly one
triangle. Mathlib splits this into two conditions: the triangles are edge-disjoint
(`EdgeDisjointTriangles`, any two triangles share at most one vertex), and every edge
lies in some triangle.
-/
#source LocallyLinear

/-!
For example, take the Paley graph on `9` vertices. Mathlib's field with `9` elements,
`GaloisField 3 2`, is not computable, so we build one that is: `𝔽₃[i]`, where
`i² = -1`. Mathlib's `QuadraticAlgebra R a b` adjoins to `R` an element `ω` with
`ω² = a + b ω`, and stores `x + y ω` as the pair `⟨x, y⟩`. It is a field if `R` is a
field and `ω² = a + b ω` has no solution in `R`. Here `-1` is not a square in
`ZMod 3`, and as with `Fact (Nat.Prime 17)` in [Paley Graphs](#section-paley-graphs),
we supply this as an instance. Mathlib has no `Fintype` instance for
`QuadraticAlgebra`, so we transfer one from `R × R`.
-/
instance : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩

instance {R : Type*} [Fintype R] {a b : R} : Fintype (QuadraticAlgebra R a b) :=
  Fintype.ofEquiv _ (QuadraticAlgebra.equivProd a b).symm

/-- The Paley graph on `9` vertices, of the field `𝔽₃[i]`, where `i² = -1`. -/
abbrev paleyGraph₉ : SimpleGraph (QuadraticAlgebra (ZMod 3) (-1) 0) :=
  paleyGraph _

/-!
The nonzero squares in `𝔽₃[i]` are `±1` and `±i`, the nonzero elements with a zero
coordinate. So two vertices are adjacent when they agree in one coordinate: they lie
in the same row or column of the `3 × 3` grid. By the parameters in
[Strongly Regular Graphs](#section-strongly-regular-graphs), it is strongly
regular with `ℓ = (9 - 5) / 4 = 1`: two adjacent vertices have exactly one common
neighbour, the third vertex of their row or column. So each edge lies in exactly one
triangle, and `paleyGraph₉` is locally linear. It has `18` edges and `6` triangles.
(We use `decide +kernel` since it can handle the recursion depth here.)
-/
example : paleyGraph₉.LocallyLinear := by decide +kernel
#eval #paleyGraph₉.edgeFinset -- 18
#eval #(paleyGraph₉.cliqueFinset 3) -- 6

/-!
[Figure: The Paley graph on $9$ vertices. Its $6$ triangles are drawn as circles, whose three arcs are edges.](https://jt496.github.io/GraphTheoryInLean/figures/paleyGraph9.svg)

Locally linear graphs are behind the proof of the corners theorem: a corner-free set
`A` gives a locally linear graph with `#A` triangles, and the removal lemma shows
that this graph has few triangles, so `A` is small.

The *Ruzsa–Szemerédi problem* asks for the largest number of edges in a locally
linear graph on `n` vertices. A locally linear graph has three times as many edges as
triangles (`LocallyLinear.card_edgeFinset`), so we can count triangles instead:
Mathlib's `ruzsaSzemerediNumberNat n` is the largest number of triangles in such a
graph.

In the other direction, sets without three-term arithmetic progressions give locally
linear graphs with many triangles: a `ThreeAPFree` subset of `{0, …, n - 1}` with `m`
elements gives a locally linear graph on `6 * n + 3` vertices with `(2 * n + 1) * m`
triangles. Behrend's construction
[Behrend 1946](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-behrend-1946)
of large `ThreeAPFree` sets then shows that `ruzsaSzemerediNumberNat n` is at least a
constant times `n² * exp (-4 * √(log n))`, which is larger than `n ^ (2 - c)` for
every `c > 0` once `n` is large.
-/
#check rothNumberNat_le_ruzsaSzemerediNumberNat
#check ruzsaSzemerediNumberNat_asymptotic_lower_bound

/-!
Mathlib does not have the upper bound `o(n²)`, but the argument for corners gives it
for every graph `G` whose triangles are edge-disjoint. Suppose that `G` has at least
`ε * n²` triangles. Deleting an edge destroys at most one triangle, so `G` is `ε`-far
from triangle-free, and the removal lemma gives at least `δ * n³` triangles, where
`δ = triangleRemovalBound ε`. But the triangles have disjoint sets of edges, so there
are at most as many triangles as edges, and hence at most `n²`. This is less than
`δ * n³` when `n > 1 / δ`.
-/
theorem EdgeDisjointTriangles.card_cliqueFinset_lt [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : G.EdgeDisjointTriangles) {ε : ℝ} (hε : 0 < ε)
    (hn : (triangleRemovalBound ε)⁻¹ < Fintype.card V) :
    (#(G.cliqueFinset 3) : ℝ) < ε * Fintype.card V ^ 2 := by
  by_contra! h
  have hδ := triangleRemovalBound_pos hε
  have hV : (0 : ℝ) < Fintype.card V := (inv_pos.2 hδ).trans hn
  -- the removal lemma gives `δ * n³` triangles
  have h₁ := (hG.farFromTriangleFree (by exact_mod_cast h)).le_card_cliqueFinset
  -- but there are at most `n² / 3` of them
  have h₂ : 3 * #(G.cliqueFinset 3) ≤ Fintype.card V ^ 2 :=
    hG.card_edgeFinset_le.trans <|
      G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow ..)
  have h₃ : (3 * #(G.cliqueFinset 3) : ℝ) ≤ Fintype.card V ^ 2 := by
    exact_mod_cast h₂
  rw [inv_lt_iff_one_lt_mul₀' hδ] at hn
  linarith [mul_lt_mul_of_pos_right hn (pow_pos hV 2)]

open Filter Asymptotics in
/--
The **Ruzsa–Szemerédi theorem**: `ruzsaSzemerediNumberNat n` is `o(n²)`, so a locally
linear graph on `n` vertices has `o(n²)` edges. This answers the Ruzsa–Szemerédi
problem up to the gap between `o(n²)` and Behrend's lower bound. -/
theorem ruzsaSzemerediNumberNat_isLittleO :
    (fun n => (ruzsaSzemerediNumberNat n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2 := by
  simp only [isLittleO_iff, eventually_atTop, norm_pow, RCLike.norm_natCast]
  -- the filter and Landau notation have gone, leaving the obvious goal
  -- ⊢ ∀ c, 0 < c → ∃ a, ∀ b, a ≤ b → ↑(ruzsaSzemerediNumberNat b) ≤ c * ↑b ^ 2
  refine fun ε hε => ⟨⌊(triangleRemovalBound ε)⁻¹⌋₊ + 1, fun n hn => ?_⟩
  obtain ⟨G, _, hG, hlin⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  have := hlin.edgeDisjointTriangles.card_cliqueFinset_lt hε
    (by simpa using Nat.lt_of_floor_lt hn)
  rw [ruzsaSzemerediNumberNat, ← hG]
  simpa using this.le

/-!
Ruzsa and Szemerédi
[Ruzsa–Szemerédi 1978](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-ruzsa-szemeredi-1978)
stated their result as the *`(6, 3)` theorem*: a family of `3`-element subsets of an
`n`-element set in which no `6` points contain `3` of the sets has `o(n²)` sets. This
follows from the graph form above. If two sets share two points, then no other set
meets them, so these pairs occupy disjoint sets of `4` points. Discard their at most
`n / 2` triples. Joining two points whenever one of the remaining triples contains
both gives a graph whose triangles are exactly those triples: an extra triangle would
have its edges supplied by three distinct triples whose union has at most `6` points,
a contradiction. Every edge lies in one of these triangles, and the triangles are
edge-disjoint, so the graph is locally linear. By the Ruzsa–Szemerédi theorem there
are `o(n²)` remaining sets. In total the family has at most `n / 2 + o(n²)` sets,
which is still `o(n²)`.

# Infinite Graphs *

Most of this guide deals with finite graphs or with infinite graphs through their
finite parts. We end with two results about the infinite structure of a graph.

## Kőnig's Lemma

*Kőnig's infinity lemma*
[Kőnig 1927](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-konig-1927)
(not to be confused with Kőnig's theorem on matchings) says that an infinite,
connected, locally finite graph contains a *ray* (a one-way infinite path). Mathlib
has the order-theoretic form of this result: in a (strongly atomic) partial order in
which each element is covered by finitely many elements, an element with infinitely
many elements above it starts an infinite chain `b = f 0 ⋖ f 1 ⋖ f 2 ⋖ ⋯` of covering
steps.
-/
#check exists_seq_covby_of_forall_covby_finite

/-!
Mathlib has no notion of a ray in a graph, so it does not yet state the graph form.
A ray in `G` is a copy of the infinite path `pathNat`, so the graph form says that
`pathNat ⊑ G` for every infinite, connected, locally finite graph `G`. We deduce it
from the order-theoretic form.

Fix a vertex `v` and order the vertices so that `u ≤ w` iff `u` lies on a shortest
path from `v` to `w`, that is, iff `G.dist v u + G.dist u w = G.dist v w`. We use
`dist` rather than `edist`: as `G` is connected, `dist` has no junk values, and the
proof cancels terms from sums, which does not work in `ℕ∞`. Inside the proof,
`let _ : PartialOrder V` makes this order a local instance, so the instance search
finds it for the rest of the proof and nowhere else.

We then check the hypotheses of Kőnig's lemma. The function `G.dist v` is strictly
monotone, so the order is well founded, and Mathlib has an instance saying that a
well-founded order is strongly atomic: if `u < w` then some `x ≤ w` covers `u`. If
`w` covers `u` then `u` and `w` are adjacent: the second vertex `x` of a shortest
walk from `u` to `w` satisfies `u ≤ x ≤ w` and `x ≠ u`, so `x = w`. So the vertices
covering `u` are neighbours of `u`, and there are finitely many of them. Finally,
every vertex lies above `v`, so infinitely many vertices do.

Kőnig's lemma now gives a chain `v = f 0 ⋖ f 1 ⋖ f 2 ⋖ ⋯` whose consecutive vertices
are adjacent. We use the version
`exists_orderEmbedding_covby_of_forall_covby_finite`, which returns the chain as an
order embedding `f : ℕ ↪o V`, so the injectivity needed for a copy of `pathNat` comes
for free.
-/
/-- **Kőnig's lemma**: an infinite, connected, locally finite graph has a ray. -/
theorem Connected.pathNat_isContained [Infinite V] [G.LocallyFinite]
    (hG : G.Connected) : pathNat ⊑ G := by
  obtain ⟨v⟩ := hG.nonempty
  -- `u ≤ w` iff `u` lies on a shortest path from `v` to `w`
  let _ : PartialOrder V :=
    { le u w := G.dist v u + G.dist u w = G.dist v w
      le_refl u := by simp
      le_trans u w x h₁ h₂ := by
        have := hG.dist_triangle (u := v) (v := u) (w := x)
        have := hG.dist_triangle (u := u) (v := w) (w := x)
        grind
      le_antisymm u w h₁ h₂ := by
        have := G.dist_comm (u := u) (v := w)
        exact hG.dist_eq_zero_iff.1 (by grind) }
  -- `G.dist v` is strictly monotone, so the order is well founded
  have hdist : StrictMono (G.dist v) := fun u w h => by
    have := hG.pos_dist_of_ne h.ne
    have : G.dist v u + G.dist u w = G.dist v w := h.le
    grind
  have : WellFoundedLT V := hdist.wellFoundedLT
  -- if `w` covers `u` then they are adjacent
  have hadj {u w : V} (h : u ⋖ w) : G.Adj u w := by
    obtain ⟨_ | @⟨_, x, _, hux, p⟩, hp⟩ := hG.exists_walk_length_eq_dist u w
    · exact absurd rfl h.ne
    rw [Walk.length_cons] at hp
    have := dist_le p
    have := dist_eq_one_iff_adj.2 hux
    have := hG.dist_triangle (u := v) (v := u) (w := x)
    have := hG.dist_triangle (u := v) (v := x) (w := w)
    have : G.dist v u + G.dist u w = G.dist v w := h.le
    obtain rfl | rfl := h.eq_or_eq (c := x)
      (show G.dist v u + G.dist u x = G.dist v x by grind)
      (show G.dist v x + G.dist x w = G.dist v w by grind)
    · exact (hux.ne rfl).elim
    · exact hux
  -- so each `u` has finitely many covers, and every vertex lies above `v`
  obtain ⟨f, -, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite
    (fun u => (G.neighborSet u).toFinite.subset fun _ h => hadj h)
    (Set.infinite_univ.mono fun w _ => (by simp : G.dist v v + G.dist v w = _))
  refine ⟨⟨⟨f, ?_⟩, f.injective⟩⟩
  rintro i j (rfl | rfl)
  · exact hadj (hf i)
  · exact (hadj (hf j)).symm

/-!
Like the De Bruijn–Erdős theorem (`colorable_of_forall_finite_subgraph_colorable`)
and Hall's theorem for infinite graphs (`exists_isMatching_of_forall_ncard_le`),
this is a *compactness* argument, deducing an infinite object from finite
information.

## Ends

The *ends* of an infinite graph describe the different ways of going to infinity.
The usual definition is in terms of rays. Two rays are *equivalent* if no finite set
of vertices separates them: for every finite set `K`, both rays have tails in the
same component of the graph with `K` deleted. An end is an equivalence class of rays.

Mathlib describes ends without rays by recording where each ray ends up. Write
`G.ComponentCompl K` for the set of components of `G - K`. Given a ray and a finite
set `K`, only finitely many vertices of the ray lie in `K`, since a copy of `pathNat`
is injective, so some tail of the ray avoids `K`. A tail is connected, so it lies in
a single component of `G - K`, and any two tails of the ray share a tail, so this
component does not depend on the choice of tail. So a ray chooses, for each finite
`K`, a component of `G - K`, and these choices are consistent: if `K ⊆ L` then the
component chosen for `L` lies inside the one chosen for `K`. Any consistent choice of
components is called a *direction*.
-/
section ends
open CategoryTheory Opposite
#source ComponentCompl -- abbrev ComponentCompl := (G.induce Kᶜ).ConnectedComponent

/-- A *direction* of `G` chooses, for every finite set `K` of vertices, a component
`f K` of `G - K`, consistently: if `K ⊆ L` then `f L ⊆ f K`. -/
def IsDirection (f : (K : Finset V) → G.ComponentCompl K) : Prop :=
  ∀ ⦃K L : Finset V⦄, K ⊆ L → (f L : Set V) ⊆ f K

/-!
Two rays give the same direction exactly when they are equivalent, and Diestel and
Kühn
[Diestel–Kühn 2003](https://jt496.github.io/GraphTheoryInLean/Bibliography/#bib-diestel-kuhn-2003)
showed that every direction comes from a ray, so ends and directions are the same
thing. Mathlib defines the ends of `G` as its directions, but phrased in the language
of category theory. `G.componentComplFunctor` is the functor sending each finite set
`K` to `G.ComponentCompl K`, and each inclusion `K ⊆ L` to the map
`ComponentCompl.hom` sending a component of `G - L` to the component of `G - K` that
contains it. These maps run from `L` to `K` (the opposite direction to the inclusion
`K ⊆ L`), so the functor is defined on the opposite category `(Finset V)ᵒᵖ`. A
direction is then a *section* of this functor: an element of each set, compatible
with all of the maps.
-/

#check componentComplFunctor -- (G : SimpleGraph V) : (Finset V)ᵒᵖ ⥤ Type u
#check SimpleGraph.end -- Set ((j : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj j)

/-!
Unwinding the definitions, the elements of `G.end` are exactly the directions. (Here
`op K` is `K` regarded as an object of `(Finset V)ᵒᵖ`.)
-/
/-- The ends of `G`, as defined in Mathlib, are exactly its directions. -/
theorem mem_end_iff {f : (K : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj K} :
    f ∈ G.end ↔ G.IsDirection fun K => f (op K) := by
  constructor <;> intro hf K L h
  · exact (ComponentCompl.hom_eq_iff_le _ (Finset.coe_subset.2 h) _).1
      (hf (opHomOfLE h))
  · exact (ComponentCompl.hom_eq_iff_le _ (Finset.coe_subset.2 (leOfHom h.unop)) _).2
      (hf (leOfHom h.unop))

/-!
A finite graph has no ends, since `G - V` is empty; Mathlib has this as an instance,
so `inferInstance` proves it.
-/
example {V : Type} [Finite V] (G : SimpleGraph V) : IsEmpty G.end := inferInstance

/-!
Kőnig's lemma reappears in the language of ends: every infinite, connected, locally
finite graph has at least one end. This follows from `Connected.pathNat_isContained`,
since the ray it gives chooses a direction as described at the start of this section
(Exercise 19), but Mathlib proves it directly, without rays. Getting a ray back from
an end takes another compactness argument (the locally finite case of the
Diestel–Kühn result above), so Mathlib's theorem does not give
`Connected.pathNat_isContained` directly.
-/
#check nonempty_ends_of_infinite

/-!
Connectivity and local finiteness ensure that `G - K` has only finitely many
components (Mathlib's instance `componentCompl_finite`). For nonempty `K`, every
component contains a neighbour of `K`, since `G` is connected, and `K` has only
finitely many neighbours, since `G` is locally finite.
-/
#check componentCompl_finite

/-!
Mathlib's proof then applies `nonempty_sections_of_finite_inverse_system`, the
compactness theorem used earlier for finite subgraphs and Hall's theorem. It
generalizes Kőnig's lemma: a functor on `(Finset V)ᵒᵖ` whose sets are all finite and
nonempty has a section. Here they are nonempty because deleting finitely many
vertices from an infinite graph leaves a vertex. Being able to reuse general
results like this is why Mathlib defines ends using category theory.

To compute the ends of a graph we need to understand the components of `G - K`. Our
main tool is the following observation: if `H` is connected and `φ : H →g G` is a
homomorphism whose image avoids `K`, then the image lies in a single component of
`G - K`.
-/
theorem ComponentCompl.mem_of_hom {W : Type*} {H : SimpleGraph W}
    (hH : H.Preconnected) (φ : H →g G) {K : Set V} (hK : ∀ w, φ w ∉ K)
    {C : G.ComponentCompl K} {u : W} (hu : φ u ∈ C) (w : W) : φ w ∈ C := by
  obtain ⟨p⟩ := hH u w
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (mem_of_adj _ _ hu (hK _) (φ.map_adj h))

/-!
This makes precise the step at the start of this section where a tail of a ray lies
in a single component: a tail of a ray `f` is the image of `pathNat` under `f`
composed with `pathNat.translate N`, and `pathNat` is connected.

Each end chooses infinite components of `G - K` (`end_componentCompl_infinite`): if
a chosen component `C` were finite, the choice outside `K ∪ C` would have to lie in
`C` while avoiding it. So to show that a graph has at most one end it is enough to
find, for each finite set `K`, a vertex lying in every infinite component of `G - K`:
any two ends then choose components sharing this vertex, which must be equal.
-/
lemma subsingleton_end_of_common_vertex {V : Type} {G : SimpleGraph V}
    (h : ∀ K : Finset V, ∃ v : V,
      ∀ C : G.ComponentCompl (K : Set V), C.supp.Infinite → v ∈ C) :
    Subsingleton G.end := by
  constructor
  rintro ⟨e, he⟩ ⟨f, hf⟩
  apply Subtype.ext
  funext K
  obtain ⟨v, hv⟩ := h K.unop
  exact ComponentCompl.pairwise_disjoint.eq (Set.not_disjoint_iff.2 ⟨v,
    hv _ (end_componentCompl_infinite _ ⟨e, he⟩ K),
    hv _ (end_componentCompl_infinite _ ⟨f, hf⟩ K)⟩)

/-!
For example, `pathNat` has exactly one end. Given a finite set `K`, choose `N` with
`K ⊆ [0, N]`. The translate `N + 1, N + 2, …` of `pathNat` avoids `K`, so it lies in
a single component of `G - K`. An infinite component contains some `m > N`, and
hence contains `N + 1`. So `N + 1` lies in every infinite component of `G - K`.
Since `pathNat` is infinite, connected and locally finite, it also has at least one
end by Kőnig's lemma (`nonempty_ends_of_infinite`).
-/
example : Nat.card pathNat.end = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨subsingleton_end_of_common_vertex fun K => ?_, ?_⟩
  · obtain ⟨N, hN⟩ := K.finite_toSet.bddAbove
    let φ := (pathNat.translate (N + 1)).toHom
    have hφ (n : ℕ) : φ n = n + (N + 1) := rfl
    have hK (n : ℕ) : φ n ∉ K := fun h => by
      have := hN h; rw [hφ] at this; grind
    -- every infinite component of `G - K` contains `N + 1`
    refine ⟨N + 1, fun C hC => ?_⟩
    obtain ⟨m, hmC, hm⟩ := hC.exists_gt N
    have h₁ : φ (m - (N + 1)) = m := by rw [hφ]; grind
    have h₂ : φ 0 = N + 1 := by rw [hφ]; grind
    exact h₂ ▸ ComponentCompl.mem_of_hom connected_pathNat.preconnected φ hK
      (h₁ ▸ hmC) 0
  · have : Fact pathNat.Preconnected := ⟨connected_pathNat.preconnected⟩
    exact (nonempty_ends_of_infinite _).to_subtype

end ends
/-!
A graph can have more than one end. The two-way infinite path `hasse ℤ` has two, one
in each direction, and the infinite binary tree has uncountably many, one for each
infinite sequence of left and right turns starting at the root. In Exercise 20 we
show that the grid `ℤ × ℤ`, by contrast, has exactly one end. Note that in Lean this
grid is the box product `hasse ℤ □ hasse ℤ`.
-/
end SimpleGraph
