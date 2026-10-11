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
import Mathlib.Order.KonigLemma
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
open Finset

/-!
There are quite a few classical theorems about graphs in Mathlib (but many more are
still missing!).

In this chapter we survey the graph-theoretic results that Mathlib formalizes,
building on the definitions of the earlier chapters. Proofs are mostly left to
Mathlib: we state each result, explain how its statement is phrased in Lean, and
apply it to our running examples. Where a natural generalization is missing from
Mathlib and easy to give we prove it ourselves.

We begin with matchings: Hall's marriage theorem and its deficiency version, which
gives Kőnig's theorem, symmetric differences of perfect matchings, and Tutte's
theorem. We then turn to extremal graph theory: Turán's theorem (with Mantel's
theorem as a special case), Füredi's stability theorem, the Andrásfai–Erdős–Sós
theorem, Zykov's theorem on the number of cliques, and the extremal numbers
`extremalNumber n H`, together with their asymptotic behaviour (Turán density and
the Erdős–Stone theorem). The two final sections are more advanced: Szemerédi's
regularity lemma and the triangle removal lemma, with Roth's theorem on arithmetic
progressions as an application, and two results about infinite graphs, Kőnig's lemma
and the existence of ends.

Many famous theorems are not (yet) in Mathlib. These include Ramsey's theorem for
graphs, the Kővári–Sós–Turán theorem, Kirchhoff's matrix-tree theorem, Cayley's
formula, Euler's circuit theorem, Euler's formula and planarity, Menger's theorem,
Brooks' theorem, Vizing's theorem, Berge's theorem, Kőnig's theorem on bipartite
matchings and the theorems of Dirac and Ore. (Some of these are proved in this guide:
[Euler's theorem](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-euler-s-theorem)
on Eulerian trails, the theorems of
[Dirac and Ore](https://jt496.github.io/GraphTheoryInLean/Walks/#section-hamiltonian-graphs-ore-dirac-and-bondy-chv-tal),
[Brooks' theorem](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-brooks-theorem)
and
[Kőnig's theorem](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-k-nig-s-theorem).)

# Matchings

Recall from
[Matching Number](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-matching-number)
that a matching in `G` is a subgraph `M : G.Subgraph` in which every vertex of `M`
has exactly one neighbour in `M`. It need not be spanning: its vertices are the
matched vertices. A perfect matching is a spanning matching, so every vertex of `G`
has exactly one `M`-neighbour.

[Figure: A matching $M$ and a perfect matching](https://jt496.github.io/GraphTheoryInLean/figures/matching.svg)
-/
example (M : G.Subgraph) : M.IsPerfectMatching ↔ ∀ v, ∃! w, M.Adj v w :=
  Subgraph.isPerfectMatching_iff

/-!
The vertices of a perfect matching are paired up, so a finite graph with a perfect
matching has an even number of vertices.
-/
#check Subgraph.IsPerfectMatching.even_card
-- M.IsPerfectMatching → Even (Fintype.card V)

/-!
For example, the Mycielskian `mμ[G]` of a finite graph has `2 * |V| + 1` vertices, an
odd number, so it never has a perfect matching.
-/
example [Finite V] (M : mμ[G].Subgraph) : ¬ M.IsPerfectMatching := fun hM => by
  have := Fintype.ofFinite V
  simpa [Fintype.card_option, Fintype.card_sum, Nat.even_add_one] using hM.even_card

/-!
The classical existence results for perfect matchings are Hall's marriage theorem
(for bipartite graphs) and Tutte's theorem (for all graphs).

## Hall's Marriage Theorem

Let `G` be bipartite with parts `p₁` and `p₂` (in Lean `G.IsBipartiteWith p₁ p₂`, see
[Bipartite Graphs](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-bipartite-graphs)).
*Hall's condition* says that every finite set `s ⊆ p₁` has at least `#s` neighbours.
*Hall's theorem* says that this condition implies that `G` has a matching saturating
`p₁`, that is, one whose vertices include all of `p₁`. (The converse is easy: the
partners of the vertices in `s` are distinct neighbours of `s`.)

[Figure: A bipartite graph with a subset $S$ and its neighbourhood $N(S)$](https://jt496.github.io/GraphTheoryInLean/figures/hall.svg)
-/
#check exists_isMatching_of_forall_ncard_le
-- [G.LocallyFinite] → G.IsBipartiteWith p₁ p₂ →
--   (∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) →
--   ∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching

/-!
Notice that `V` need not be finite: `G` only needs to be locally finite. Hall's
condition is stated with `Set.ncard`, which is `0` on infinite sets, so it holds
trivially for infinite `s` and only finite sets need to be checked.
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
-- [G.LocallyFinite] → G.IsBipartiteWith p₁ p₂ →
--   (∀ s, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) → ∃ M, M.IsPerfectMatching

/-!
For infinite graphs the proof deduces the theorem from the finite case by
compactness, as for the De Bruijn–Erdős theorem
([De Bruijn–Erdős Theorem](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-de-bruijn-erd-s-theorem)).
Each finite `F ⊆ p₁` has at least one injective choice of neighbours, by the finite
case, and only finitely many, since each vertex has finitely many neighbours: this is
where local finiteness is used. A compactness theorem then gives choices on all the
sets `F` that agree with each other, and together they choose a neighbour for every
vertex of `p₁`.
-/
#check nonempty_sections_of_finite_inverse_system
-- an inverse system of finite nonempty sets has a compatible family of elements

/-!
For a perfect matching, the same argument applied to all of `V` at once gives an
injective choice of a neighbour for every vertex, which is why the condition is
stated for all sets of vertices. As `G` is bipartite, this choice restricts to
injections `p₁ → p₂` and `p₂ → p₁` along edges. If `V` is finite then
`|p₁| = |p₂|`, and either one is already a perfect matching. In general they are
combined as in the proof of the Schröder–Bernstein theorem, which Mathlib proves for
injections along any relation `R`. With `R` the adjacency relation, the bijection it
produces is a perfect matching.
-/
#check Function.Embedding.schroeder_bernstein_of_rel
-- Injective f → Injective g → (∀ a, R a (f a)) → (∀ b, R (g b) b) →
--   ∃ h, Function.Bijective h ∧ ∀ a, R a (h a)

/-!
Behind both lies the classical statement about *systems of distinct representatives*:
a family of finite sets `t : ι → Finset α` has an injective choice function iff every
union of `k` of the sets has at least `k` elements. Mathlib states it for any index
type, even an infinite one.
-/
#check Finset.all_card_le_biUnion_card_iff_exists_injective
-- (∀ s, #s ≤ #(s.biUnion t)) ↔ ∃ f, Function.Injective f ∧ ∀ x, f x ∈ t x

/-!
Applied to the neighbourhoods of the vertices of `p₁`, it chooses a different
neighbour for each vertex. In a bipartite graph the edges to the chosen neighbours
form a matching, by Mathlib's construction of a matching from a bijection between
disjoint sets.
-/
#check Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
-- Disjoint s t → (f : s ≃ t) → (∀ v, G.Adj v (f v)) →
--   ∃ M, M.verts = s ∪ t ∧ M.IsMatching

/-!
An injective choice of neighbours `f` for the vertices of `X ⊆ p₁` gives a
matching covering `X`: the union of the edges `x — f x`.
-/
lemma exists_isMatching_of_injective {p₁ p₂ X : Set V} (h₁ : G.IsBipartiteWith p₁ p₂)
    (hX : X ⊆ p₁) (f : X → V) (hf : Function.Injective f)
    (hadj : ∀ x : X, G.Adj x (f x)) :
    ∃ M : Subgraph G, X ⊆ M.verts ∧ M.IsMatching := by
  have hd : Disjoint X (Set.range f) := h₁.disjoint.mono hX
    (Set.range_subset_iff.mpr fun x =>
      h₁.mem_of_mem_adj (hX x.2) (hadj x))
  obtain ⟨M, hverts, hM⟩ :=
    Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
      hd (Equiv.ofInjective f hf) hadj
  exact ⟨M, hverts ▸ Set.subset_union_left, hM⟩

/-!
Local finiteness cannot be dropped from the classical theorem. Let `a` be adjacent to
`c₁, c₂, …` and let each `bᵢ` be adjacent only to `cᵢ`. Every finite set of the
vertices `a, b₁, b₂, …` has at least as many neighbours as elements, but no matching
covers them all: whichever `cᵢ` is matched to `a`, the vertex `bᵢ` is left over.

In Lean, though, this graph fails Hall's condition for `{a}`: `a` has infinitely many
neighbours, so the `ncard` of its neighbourhood is `0`.
-/
example {a : V} (ha : (G.neighborSet a).Infinite) :
    ¬ ({a} : Set V).ncard ≤ (⋃ x ∈ ({a} : Set V), G.neighborSet x).ncard := by
  simp [ha.ncard]

/-!
So Lean's form of Hall's condition already forces every vertex of `p₁` to have a
finite neighbourhood. Mathlib's proof applies the theorem on systems of distinct
representatives to the finsets `G.neighborFinset x`, and it is to form these that
it assumes `[G.LocallyFinite]`. Applying the theorem instead to the neighbourhoods
of the vertices of `p₁`, which are finite by Hall's condition, we can drop this
assumption. The vertices of `p₂` may then have infinite degree: for example, let
`p₁ = {b₁, b₂, …}` and `p₂ = {c₁, c₂, …} ∪ {z}`, with `bᵢ — cᵢ` and `z` adjacent
to every `bᵢ`.
-/
/-- One-sided Hall without `[G.LocallyFinite]`. -/
theorem exists_isMatching_of_forall_ncard_le' {p₁ p₂ : Set V}
    (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, p₁ ⊆ M.verts ∧ M.IsMatching := by
  classical
  have hfin (x : p₁) : (G.neighborSet x).Finite := by
    apply Set.finite_of_ncard_pos
    simpa [Nat.succ_le_iff] using h₂ {x.1} (by simp)
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x : p₁ ↦ (hfin x).toFinset) |>.mp fun s ↦ by
    have := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset,
      Finset.card_image_of_injective _ Subtype.val_injective] at this
    simpa [← Set.ncard_coe_finset] using this
  exact exists_isMatching_of_injective h₁ subset_rfl f hf₁ fun x : p₁ ↦ by
    simpa using hf₂ x

/-!
## Kőnig's Theorem

In
[Matching Number](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-matching-number)
we proved weak duality `ν G ≤ τ G`: a vertex cover needs a vertex from each edge of a
matching. *Kőnig's theorem* says that for bipartite graphs this is an equality. It is
not in Mathlib, and we deduce it from a *deficiency version* of Hall's theorem.

Suppose that every finite `s ⊆ p₁` has at least `|s| - d` neighbours. Then we can
match all but at most `d` vertices of `p₁`. If `p₁` has at most `d` vertices the
empty matching will do. Otherwise each `x ∈ p₁` has a finite neighbourhood: if not,
then `x` and `d` other vertices of `p₁` would violate the condition, since an
infinite neighbourhood has `ncard` equal to `0`. Next, add `d` new vertices adjacent
to every vertex of `p₁`. Hall's condition now holds, so the systems of distinct
representatives theorem gives an injective choice of neighbours `g`, with values in
`V ⊕ Fin d`. At most `d` vertices of `p₁` are sent to new vertices, and the others
are sent injectively to neighbours in `G`, which gives a matching.
-/
/-- **Hall's theorem with deficiency `d`**: if every `s ⊆ p₁` has at least
`|s| - d` neighbours, then a matching covers all but at most `d` vertices of `p₁`. -/
theorem exists_isMatching_of_forall_ncard_le_add {p₁ p₂ : Set V} {d : ℕ}
    (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard + d) :
    ∃ M : Subgraph G, M.IsMatching ∧ (p₁ \ M.verts).encard ≤ d := by
  classical
  -- if `p₁` has at most `d` vertices, the empty matching will do
  rcases le_or_gt p₁.encard d with hp | hp
  · exact ⟨⊥, Subgraph.isMatching_bot, by simpa using hp⟩
  -- otherwise each `x ∈ p₁` has a finite neighbourhood: apply the condition to `x`
  -- and `d` more vertices of `p₁`
  have hfin (x : p₁) : (G.neighborSet x).Finite := by
    by_contra hinf
    rw [← Set.encard_sdiff_singleton_add_one x.2] at hp
    obtain ⟨t, ht, htd⟩ := Set.exists_subset_encard_eq (Order.le_of_lt_add_one hp)
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htd
    have hxt : (x : V) ∉ t := fun h => (ht h).2 rfl
    have hs := h₂ (insert (x : V) t)
      (Set.insert_subset x.2 (ht.trans Set.sdiff_subset))
    have hN : (⋃ y ∈ insert (x : V) t, G.neighborSet y).Infinite :=
      Set.Infinite.mono (Set.subset_biUnion_of_mem (Set.mem_insert _ _)) hinf
    rw [hN.ncard, Set.ncard_insert_of_notMem hxt htfin] at hs
    have : t.ncard = d := by exact_mod_cast htfin.cast_ncard_eq.trans htd
    grind
  let : ∀ x : p₁, Fintype (G.neighborSet x) := fun x => (hfin x).fintype
  -- each vertex of `p₁` may choose a neighbour, or one of `d` new vertices
  let t : p₁ → Finset (V ⊕ Fin d) := fun x =>
    (G.neighborFinset x).map .inl ∪ univ.map .inr
  obtain ⟨g, hg₁, hg₂⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1
    fun s => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
      · simp
      have hs := h₂ (s.image Subtype.val) (by simp)
      rw [Set.ncard_coe_finset,
        card_image_of_injective _ Subtype.val_injective] at hs
      have hN : (⋃ x ∈ (s.image Subtype.val : Set V), G.neighborSet x) =
          ((s.biUnion fun x => G.neighborFinset x) : Set V) := by
        ext
        simp
      rw [hN, Set.ncard_coe_finset] at hs
      have : s.biUnion t = (s.biUnion fun x => G.neighborFinset x).map .inl ∪
          univ.map .inr := by
        ext (v | i)
        · simp [t]
        · simpa [t] using ⟨x₀.1, x₀.2, hx₀⟩
      rw [this, card_union_of_disjoint (disjoint_map_inl_map_inr _ _), card_map,
        card_map, card_univ, Fintype.card_fin]
      exact hs
  -- the vertices `X` of `p₁` that chose an old vertex are matched in `G`
  let X : Set V := {x | ∃ hx : x ∈ p₁, (g ⟨x, hx⟩).isLeft}
  have hX : X ⊆ p₁ := fun x hx => hx.1
  let f : X → V := fun x => (g ⟨x, x.2.1⟩).getLeft x.2.2
  have hgf (x : X) : g ⟨x, x.2.1⟩ = .inl (f x) := (Sum.inl_getLeft _ _).symm
  have hf : Function.Injective f := fun x y hxy => by
    have := hg₁ ((hgf x).trans (hxy ▸ (hgf y).symm))
    exact Subtype.ext (congrArg (fun z : p₁ => (z : V)) this)
  have hadj (x : X) : G.Adj x (f x) := by
    simpa [t, hgf x] using hg₂ ⟨x, x.2.1⟩
  obtain ⟨M, hXM, hM⟩ := exists_isMatching_of_injective h₁ hX f hf hadj
  refine ⟨M, hM,
    le_trans (Set.encard_le_encard (Set.sdiff_subset_sdiff_right hXM)) ?_⟩
  -- the other vertices of `p₁` chose distinct new vertices
  have hp (x : ↥(p₁ \ X)) : (x : V) ∈ p₁ := x.2.1
  have hr (x : ↥(p₁ \ X)) : (g ⟨x, hp x⟩).isRight := by
    simpa [X, hp x] using x.2.2
  let φ : ↥(p₁ \ X) → Fin d := fun x => (g ⟨x, hp x⟩).getRight (hr x)
  have hgφ (x : ↥(p₁ \ X)) : g ⟨x, hp x⟩ = .inr (φ x) := (Sum.inr_getRight _ _).symm
  have hφ : Function.Injective φ := fun x y hxy => by
    have := hg₁ ((hgφ x).trans (hxy ▸ (hgφ y).symm))
    exact Subtype.ext (congrArg (fun z : p₁ => (z : V)) this)
  simpa using ENat.card_le_card_of_injective hφ

/-!
The case `d = 0` is `exists_isMatching_of_forall_ncard_le'`, Hall's theorem without
`[G.LocallyFinite]`.
-/
example {p₁ p₂ : Set V} (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, p₁ ⊆ M.verts ∧ M.IsMatching := by
  obtain ⟨M, hM, h⟩ := exists_isMatching_of_forall_ncard_le_add (d := 0) h₁ h₂
  exact ⟨M, Set.sdiff_eq_empty.1 (by simpa using h), hM⟩

/-!
Now let `s₀ ⊆ p₁` have the largest deficiency `d = |s₀| - |N(s₀)|`, where `N(s)` is
the set of neighbours of `s`. Every `s ⊆ p₁` has at least `|s| - d` neighbours, so
there is a matching with at least `|p₁| - d` edges (by
`Subgraph.IsMatching.ncard_inter_le` from
[Matching Number](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-matching-number)).
On the other hand the vertices of `p₁` outside `s₀`, together with `N(s₀)`, form a
vertex cover: an edge with its end in `p₁` either leaves `p₁ \ s₀` or ends in
`N(s₀)`. This vertex cover has `|p₁| - |s₀| + |N(s₀)| = |p₁| - d` vertices, so
`τ G ≤ ν G`.
-/
/-- **Kőnig's theorem**: in a finite bipartite graph the matching number equals the
vertex cover number. -/
theorem IsBipartite.matchingNum_eq_vertexCoverNum [Finite V] (h : G.IsBipartite) :
    ν G = τ G := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨p₁, p₂, h₁⟩ := h.exists_isBipartiteWith
  refine le_antisymm G.matchingNum_le_vertexCoverNum ?_
  -- choose `s₀ ⊆ p₁` of maximum deficiency `|s₀| - |N(s₀)|`
  obtain ⟨s₀, hs₀, hmax⟩ :=
    (Set.toFinite {s : Set V | s ⊆ p₁}).toFinset.exists_max_image
      (fun s => (s.ncard : ℤ) - (⋃ x ∈ s, G.neighborSet x).ncard) ⟨∅, by simp⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs₀ hmax
  set N₀ := ⋃ x ∈ s₀, G.neighborSet x
  set d := s₀.ncard - N₀.ncard
  -- the deficiency of `s₀` is at least that of `∅`, which is `0`
  have h0 : N₀.ncard ≤ s₀.ncard := by simpa using hmax ∅ (Set.empty_subset _)
  obtain ⟨M, hM, hMd⟩ := exists_isMatching_of_forall_ncard_le_add (d := d) h₁
    fun s hs => by grind
  -- `(p₁ \ s₀) ∪ N₀` is a vertex cover
  have hC : G.IsVertexCover ((p₁ \ s₀) ∪ N₀) := by
    have key {a b : V} (ha : a ∈ p₁) (hab : G.Adj a b) :
        a ∈ (p₁ \ s₀) ∪ N₀ ∨ b ∈ (p₁ \ s₀) ∪ N₀ := by
      by_cases has : a ∈ s₀
      · exact .inr (.inr (Set.mem_biUnion has hab))
      · exact .inl (.inl ⟨ha, has⟩)
    intro u v huv
    rcases h₁.mem_of_adj huv with ⟨hu, -⟩ | ⟨-, hv⟩
    · exact key hu huv
    · exact (key hv huv.symm).symm
  -- it has at most `|p₁| - d` vertices, and `M` has at least `|p₁| - d` edges
  have hMd' : (p₁ \ M.verts).ncard ≤ d := by
    rwa [← Set.Finite.cast_ncard_eq (Set.toFinite _), Nat.cast_le] at hMd
  have := Set.ncard_union_le (p₁ \ s₀) N₀
  have := Set.ncard_sdiff_add_ncard_of_subset hs₀
  have := Set.ncard_inter_add_ncard_sdiff_eq_ncard p₁ M.verts
  have := hM.ncard_inter_le h₁
  calc τ G ≤ ((p₁ \ s₀) ∪ N₀).encard := hC.vertexCoverNum_le
    _ = ((p₁ \ s₀) ∪ N₀).ncard := (Set.Finite.cast_ncard_eq (Set.toFinite _)).symm
    _ ≤ M.edgeSet.ncard := by
      norm_cast
      grind
    _ = M.edgeSet.encard := Set.Finite.cast_ncard_eq (Set.toFinite _)
    _ ≤ ν G := hM.le_matchingNum

/-!
The hypercube `Q[n + 1]` is bipartite
([Colouring Hypercubes](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-colouring-hypercubes))
and has matching number `2 ^ n`
([Matching Number of the Hypercube](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-matching-number-of-the-hypercube)).
So also has vertex cover number `2 ^ n`.
-/
example (n : ℕ) : τ Q[n + 1] = 2 ^ n := by
  rw [← (hypercube_isBipartite _).matchingNum_eq_vertexCoverNum,
    hypercube.matchingNum_succ]

/-!
## Symmetric Differences of Matchings

The classical approach to matchings studies the symmetric difference of two
matchings. Since each vertex has exactly one edge in each of two perfect matchings
`M` and `N`, every vertex of `M ∆ N` has degree `0` or `2`, so `M ∆ N` is a union
of disjoint cycles (finite or infinite) whose edges alternate between `M` and `N`.
Mathlib states this for `SimpleGraph`s rather than subgraphs, so the matchings are
first converted with `spanningCoe`.
-/
#source IsCycles -- ∀ ⦃v⦄, (G.neighborSet v).Nonempty → (G.neighborSet v).ncard = 2

#check Subgraph.IsPerfectMatching.symmDiff_isCycles
-- (M.spanningCoe ∆ M'.spanningCoe).IsCycles

#check Subgraph.IsPerfectMatching.isAlternating_symmDiff_left
-- (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M.spanningCoe

/-!
This is the machinery behind Mathlib's proof of Tutte's theorem below. Berge's
theorem (a matching is maximum iff it has no augmenting path), the usual next step,
is not in Mathlib.

A related result describes the matchings inside a clique: a finite clique can be
covered exactly by a matching iff it has an even number of vertices.
-/
#check IsClique.even_iff_exists_isMatching
-- G.IsClique u → u.Finite → (Even u.ncard ↔ ∃ M, M.verts = u ∧ M.IsMatching)

/-!
## Tutte's Theorem

Tutte's theorem characterizes the graphs with a perfect matching, bipartite or not.
If `G` has a perfect matching and we delete a set `U` of vertices, then each odd
component of what remains, i.e. `G - U` must have a vertex matched into `U`, so there
are at most `|U|` odd components. A set `U` with more than `|U|` odd components is
called a *Tutte violator*. Tutte's theorem says that `G` has a perfect matching iff
there is no Tutte violator.

[Figure: A Tutte violator $U$ with three odd components of $G \setminus U$](https://jt496.github.io/GraphTheoryInLean/figures/tutte.svg)
-/
#source SimpleGraph.IsTutteViolator

/-!
Here `G - U` is the subgraph `(⊤ : G.Subgraph).deleteVerts U`, viewed as a simple
graph via `coe`, and its odd components are counted using the connected components of
[Connectivity](https://jt496.github.io/GraphTheoryInLean/Connectivity/#chapter-connectivity).
Mathlib proves Tutte's theorem for `[Finite V]`.

A perfect matching has no Tutte violator.
-/
#check SimpleGraph.not_isTutteViolator_of_isPerfectMatching
-- M.IsPerfectMatching → ¬G.IsTutteViolator u

/-!
*Tutte's theorem*: `G` has a perfect matching iff it has no Tutte violator.
-/
#check SimpleGraph.tutte
-- (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ ∀ (u : Set V), ¬G.IsTutteViolator u

/-!
# Extremal Graph Theory

Extremal graph theory asks how many edges a graph on `n` vertices can have while
avoiding a given subgraph. The foundational result is *Turán's theorem*, which
answers this question when the forbidden subgraph is a complete graph. Recall from
[Cliques](https://jt496.github.io/GraphTheoryInLean/Cliques/#chapter-cliques) that
`G.CliqueFree (r + 1)` says that `G` has no clique of size `r + 1`.

## Turán Graphs

The extremal graphs are the Turán graphs. Mathlib defines `turanGraph n r` on
`Fin n`, with `v` and `w` adjacent iff they have different residues modulo `r`.

[Figure: The Turán graph $T(9, 3)$](https://jt496.github.io/GraphTheoryInLean/figures/turan.svg)
-/
#source turanGraph

/-!
The residue classes modulo `r` are the parts, and two vertices are adjacent iff they
lie in different parts, so this is a complete `r`-partite graph. Its parts are
*balanced*: the residue classes of `0, …, n - 1` modulo `r` have sizes `⌊n / r⌋` or
`⌈n / r⌉`. For example, when `r` divides `n` the Turán graph `turanGraph n r` is
isomorphic to Mathlib's `completeEquipartiteGraph r (n / r)`, which has `r` parts of
size `n / r`.
-/
#check completeEquipartiteGraph.turanGraph
-- completeEquipartiteGraph r t ≃g turanGraph (r * t) r

/-!
The case `r = 0` is a junk value. Since `v % 0 = v` in Lean, any two distinct
vertices are adjacent, so `turanGraph n 0 = ⊤`. This graph has edges, but there is no
such thing as a complete `0`-partite graph on a nonempty vertex set. So results
about Turán graphs usually assume `0 < r`.
-/
#check turanGraph_zero -- turanGraph n 0 = ⊤

#check turanGraph_cliqueFree -- 0 < r → (turanGraph n r).CliqueFree (r + 1)

/-!
The number of edges of `turanGraph n r` is called `turanNumber n r`. Turán graphs
have decidable adjacency, so we can compute it.
-/
#eval turanNumber 10 3 -- 33

#check turanNumber_eq
-- turanNumber n r = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2

/-!
In particular `turanNumber n r` is at most `(1 - 1/r) n²/2`.
-/
#check mul_turanNumber_le -- 2 * r * turanNumber n r ≤ (r - 1) * n ^ 2

/-!
## Turán's Theorem

Mathlib calls a graph `G` *Turán-maximal* if it is `(r + 1)`-clique-free and has at
least as many edges as any other `(r + 1)`-clique-free graph on the same vertices.
This is an instance of `IsExtremal`, which says that a graph has the most edges
among the graphs on its vertex type with a given property.
-/
#source IsExtremal
#source IsTuranMaximal

/-!
Turán's theorem says that for `0 < r` the Turán-maximal graphs are exactly the graphs
isomorphic to the Turán graph. So the Turán graph is the unique extremal graph up to
isomorphism.
-/
#check isTuranMaximal_iff_nonempty_iso_turanGraph
-- 0 < r → (G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (Fintype.card V) r))

example : (turanGraph 6 2).IsTuranMaximal 2 :=
  isTuranMaximal_turanGraph (by norm_num)

/-!
The version of Turán's theorem that is usually quoted is the resulting upper bound on
the number of edges.
-/
#check CliqueFree.card_edgeFinset_le
-- G.CliqueFree (r + 1) → #G.edgeFinset ≤ turanNumber (Fintype.card V) r

/-!
In terms of the clique number `ω` of
[Clique Number](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-clique-number):
a finite graph with `ω G ≤ r` has no `(r + 1)`-clique, so it has at most
`turanNumber n r` edges.
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ} (h : ω G ≤ r) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) r :=
  CliqueFree.card_edgeFinset_le fun s hs => by
    have := hs.le_cliqueNum
    grind

/-!
Mathlib's proof of Turán's theorem uses *Zykov symmetrization*: replacing a vertex
`t` by a copy of a non-adjacent vertex `s` (giving `t` exactly the neighbours of `s`)
cannot create an `(r + 1)`-clique, and it removes the edges at `t` while adding as
many edges as `s` has. This operation is `replaceVertex`. In a Turán-maximal graph no
such replacement can increase the number of edges, so non-adjacent vertices have the
same degree (`IsTuranMaximal.degree_eq_of_not_adj`). It follows that non-adjacency is
transitive (`IsTuranMaximal.not_adj_trans`), so the graph is complete multipartite.
We will explore Zykov symmetrization in much more detail below when we prove Zykov's
generalisation of Turán's theorem.
-/
#source replaceVertex

/-!
## Mantel's Theorem

The case `r = 2` of Turán's theorem is *Mantel's theorem*: a triangle-free graph on
`n` vertices has at most `⌊n² / 4⌋` edges. Equality holds for the balanced complete
bipartite graph `turanGraph n 2`.
-/
#check turanNumber_two -- turanNumber n 2 = n ^ 2 / 4

/-!
For example, the odd cycle `C[7]` is triangle-free, so it has at most `⌊49 / 4⌋ = 12`
edges. (`decide` checks that `C[7]` is triangle-free using the `Decidable` instance
for `CliqueFree` from
[The Finset of n-Cliques](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-the-finset-of-n-cliques).)
-/
example : #C[7].edgeFinset ≤ 7 ^ 2 / 4 := by
  rw [← turanNumber_two]
  exact CliqueFree.card_edgeFinset_le (by decide)

/-!
By
[Triangle-Free Mycielskians](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-triangle-free-mycielskians),
the Mycielskian of a triangle-free graph on `n` vertices is a triangle-free graph on
`2n + 1` vertices, so Mantel's theorem bounds its number of edges by
`⌊(2n + 1)² / 4⌋`. For the Grötzsch graph `mμ[C[5]]` this bound is `30`, while the
graph has `20` edges.
-/
#eval #mμ[C[5]].edgeFinset -- 20

/-!
The same applies to every iterated Mycielskian `mμ^n C[5]`: its clique number is
always `2`
([Clique Number of the Mycielskian](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-clique-number-of-the-mycielskian)),
so Mantel's theorem bounds its number of edges, even though its chromatic number
`n + 3` grows without bound
([Colouring Mycielskians](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-colouring-mycielskians)).
-/

/-!
Bipartite graphs are triangle-free, so they also have at most `⌊n² / 4⌋` edges.
Mathlib states this for all bipartite graphs, using `ℕ∞`-valued cardinalities so
that no finiteness assumption is needed.
-/
#check IsBipartite.four_mul_encard_edgeSet_le
-- G.IsBipartite → 4 * G.edgeSet.encard ≤ ENat.card V ^ 2

/-!
## Füredi's Stability Theorem

Turán's theorem says that the Turán graph is the only `(r + 1)`-clique-free graph on
`n` vertices with `turanNumber n r` edges. A *stability theorem* says that: any
`(r + 1)`-clique-free graph with almost that many edges is almost `r`-colourable.
Füredi gave a short proof of a sharp version of this. If `G` is `(r + 1)`-clique-free
and has `turanNumber n r - t` edges, then deleting at most `t` edges of `G` leaves an
`r`-colourable graph. We prove this below in the following form: there is an
`r`-colourable subgraph `H ≤ G` with `2 * e(G) ≤ turanNumber n r + e(H)`, where
`e(·)` is the number of edges.

Since `e(H) ≤ e(G)` this implies the bound `e(G) ≤ turanNumber n r`, so it looks like
we have a new proof of Turán's theorem. This isn't quite the case: because we need to
use Turán's theorem for complete `r`-partite graphs. However this special case is
much easier to prove than the full Turán bound: in a complete `r`-partite graph,
moving a vertex to a part with at least two fewer vertices increases the number of
edges, so the balanced one, `turanGraph n r`, maximizes the number of edges.

The proof idea goes back to Erdős. Pick a vertex `x` of maximum degree and put all of
its non-neighbours into one part. Each of them has at most `deg x` neighbours, which
is the number of vertices outside their part. Then continue inside the neighbourhood
of `x`, which is `r`-clique-free since `x` is adjacent to all of it. To make the
induction on `r` work we prove a statement about a set `S` of vertices that contains
no `(r + 1)`-clique, and record the parts as the colour classes of a function
`c : V → ℕ` taking values below `r` on `S`. For `v ∈ S` the number of neighbours of
`v` in `S` is `G.degIn S v`
([Neighbours in a Set](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-neighbours-in-a-set)).
Then the key inequality is:

`∑ v ∈ S, (G.degIn S v + #{w ∈ S | G.Adj v w ∧ c w = c v})` is at most
`∑ v ∈ S, #{w ∈ S | c w ≠ c v}`.

The left-hand side is twice the number of edges in `S` plus twice the number of edges
whose endpoints have the same colour. The right-hand side is twice the number of
edges of the complete multipartite graph whose parts are the colour classes.

In the induction step we split `S` into `N = S ∩ N(x)`, the neighbours of `x` in `S`,
and the set `Vᵣ` of non-neighbours of `x`. We colour `Vᵣ` with the new colour `r`.
Each of the three sums over `S` then splits into four blocks, according to whether
`v` and `w` lie in `N` or in `Vᵣ`.
-/
lemma sum_card_filter_union [DecidableEq V] {s t : Finset V} (h : Disjoint s t)
    (p : V → V → Prop) [DecidableRel p] :
    ∑ v ∈ s ∪ t, #{w ∈ s ∪ t | p v w} =
      ∑ v ∈ s, #{w ∈ s | p v w} + ∑ v ∈ s, #{w ∈ t | p v w} +
        ∑ v ∈ t, #{w ∈ s | p v w} + ∑ v ∈ t, #{w ∈ t | p v w} := by
  simp [sum_union h, filter_union, card_union_of_disjoint (disjoint_filter_filter h),
        sum_add_distrib, add_assoc]

/-!
The edges between `N` and `Vᵣ` are counted once from each side, and the double
counting lemma `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` says that the two
counts agree.
-/
lemma sum_degIn_comm [DecidableRel G.Adj] (s t : Finset V) :
    ∑ v ∈ s, G.degIn t v = ∑ v ∈ t, G.degIn s v := by
  simpa [degIn, bipartiteAbove, bipartiteBelow, adj_comm] using
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s) (t := t) G.Adj

/-!
The induction step only uses that `Vᵣ` is a new colour class whose vertices have at
most `#N` neighbours in `S`, which holds because `x` has maximum degree. We state it
for any disjoint `N` and `A` and a colouring `c` that is less than `r` on `N` and
equal to `r` on `A`.
-/
lemma furedi_step [DecidableRel G.Adj] [DecidableEq V] {N A : Finset V} {c : V → ℕ}
    {r : ℕ} (hNA : Disjoint N A) (hN : ∀ v ∈ N, c v < r) (hA : ∀ v ∈ A, c v = r)
    (hdeg : ∀ v ∈ A, G.degIn (N ∪ A) v ≤ #N)
    (hc : ∑ v ∈ N, (G.degIn N v + #{w ∈ N | G.Adj v w ∧ c w = c v}) ≤
      ∑ v ∈ N, #{w ∈ N | c w ≠ c v}) :
    ∑ v ∈ N ∪ A, (G.degIn (N ∪ A) v + #{w ∈ N ∪ A | G.Adj v w ∧ c w = c v}) ≤
      ∑ v ∈ N ∪ A, #{w ∈ N ∪ A | c w ≠ c v} := by
  -- colours on `N` differ from those on `A`, which all equal `r`
  have hne : ∀ v ∈ N, ∀ w ∈ A, c v ≠ c w := fun v hv w hw => by
    rw [hA w hw]; exact (hN v hv).ne
  -- the blocks other than `N × N`
  have m1 : ∑ v ∈ N, #{w ∈ A | G.Adj v w ∧ c w = c v} = 0 :=
    sum_eq_zero fun v hv => card_eq_zero.2 <| filter_false_of_mem fun w hw h =>
      hne v hv w hw h.2.symm
  have m2 : ∑ v ∈ A, #{w ∈ N | G.Adj v w ∧ c w = c v} = 0 :=
    sum_eq_zero fun v hv => card_eq_zero.2 <| filter_false_of_mem fun w hw h =>
      hne w hw v hv h.2
  have m3 : ∑ v ∈ A, #{w ∈ A | G.Adj v w ∧ c w = c v} = ∑ v ∈ A, G.degIn A v :=
    sum_congr rfl fun v hv => congrArg card <| filter_congr fun w hw => by
      simp [hA v hv, hA w hw]
  have d1 : ∑ v ∈ N, #{w ∈ A | c w ≠ c v} = #N * #A := by
    rw [sum_const_nat fun v hv => congrArg card <| filter_true_of_mem fun w hw =>
      (hne v hv w hw).symm]
  have d2 : ∑ v ∈ A, #{w ∈ N | c w ≠ c v} = #A * #N := by
    rw [sum_const_nat fun v hv => congrArg card <| filter_true_of_mem fun w hw =>
      hne w hw v hv]
  have d3 : ∑ v ∈ A, #{w ∈ A | c w ≠ c v} = 0 :=
    sum_eq_zero fun v hv => card_eq_zero.2 <| filter_false_of_mem fun w hw h =>
      h (by rw [hA v hv, hA w hw])
  -- the vertices of `A` have at most `#N` neighbours in `N ∪ A`
  have hD : ∑ v ∈ A, G.degIn N v + ∑ v ∈ A, G.degIn A v ≤ #A * #N := by
    rw [← sum_add_distrib, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun v hv => (degIn_union _ _ _ hNA).symm.le.trans (hdeg v hv)
  have e1 := sum_card_filter_union hNA G.Adj
  have e2 := sum_card_filter_union hNA (fun v w => G.Adj v w ∧ c w = c v)
  have e3 := sum_card_filter_union hNA (fun v w => c w ≠ c v)
  have hdc := sum_degIn_comm (G := G) N A
  simp only [degIn] at hc hD hdc m3 ⊢
  rw [sum_add_distrib] at hc ⊢
  grind

/-!
The local form of Füredi's inequality, proved by induction on `r`: a set `S` with
no `(r + 1)`-clique has a colouring `c` with less than `r` colours on `S` such that
the edges of `G` in `S`, plus those with both endpoints of the same colour, number
at most the edges of the complete multipartite graph with the colour classes as
parts.
-/
lemma furedi_aux [DecidableRel G.Adj] (r : ℕ) :
    ∀ S : Finset V, (∀ t ⊆ S, ¬ G.IsNClique (r + 1) t) →
      ∃ c : V → ℕ, (∀ v ∈ S, c v < r) ∧
        ∑ v ∈ S, (G.degIn S v + #{w ∈ S | G.Adj v w ∧ c w = c v}) ≤
          ∑ v ∈ S, #{w ∈ S | c w ≠ c v} := by
  classical
  induction r with
  | zero =>
    -- a set with no `1`-clique is empty
    intro S hS
    obtain rfl : S = ∅ := by
      by_contra h
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 h
      exact hS {x} (by simpa) (by simp)
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
For the whole vertex set the right-hand side counts the edges of the complete
`r`-partite graph `K` in which two vertices are adjacent iff they have different
colours, and Turán's theorem bounds these by `turanNumber n r`. The subgraph `H` is
`G ⊓ K`: we keep the edges of `G` whose endpoints have different colours.
-/
/-- **Füredi's stability theorem**: an `(r + 1)`-clique-free graph `G` has an
`r`-colourable subgraph `H` with `2 * e(G) ≤ turanNumber n r + e(H)`. So `G` can be
made `r`-colourable by deleting at most `turanNumber n r - e(G)` edges. -/
theorem CliqueFree.exists_colorable_two_mul_card_edgeFinset_le [Fintype V]
    [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1)) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj), H ≤ G ∧ H.Colorable r ∧
      2 * #G.edgeFinset ≤ turanNumber (Fintype.card V) r + #H.edgeFinset := by
  classical
  obtain ⟨c, hcr, hc⟩ := furedi_aux (G := G) r univ fun t _ ht => h t ht
  -- the complete multipartite graph whose parts are the colour classes of `c`
  let K : SimpleGraph V := (⊤ : SimpleGraph ℕ).comap c
  have hK : ∀ u v, K.Adj u v ↔ c u ≠ c v := fun u v => by simp [K]
  have hKcol : K.Colorable r :=
    ⟨Coloring.mk (fun v => (⟨c v, hcr v (mem_univ v)⟩ : Fin r)) fun {u v} huv => by
      simpa [Fin.ext_iff] using (hK u v).1 huv⟩
  refine ⟨G ⊓ K, inferInstance, inf_le_left, hKcol.mono_left inf_le_right, ?_⟩
  have hdeg (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
      H.degree v = #{w | H.Adj v w} := by
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have dK : ∀ v, K.degree v = #{w | c w ≠ c v} := fun v => by
    simp [hdeg, hK, eq_comm]
  -- `deg_G v` splits into the edges of `G ⊓ K` at `v` and the monochromatic ones
  have dGH : ∀ v, G.degree v = (G ⊓ K).degree v + #{w | G.Adj v w ∧ c w = c v} :=
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
    exact sum_congr rfl fun v _ => dGH v
  have := (hKcol.cliqueFree (Nat.lt_succ_self r)).card_edgeFinset_le
  have := sum_degrees_eq_twice_card_edges K
  have := sum_degrees_eq_twice_card_edges G
  have := sum_degrees_eq_twice_card_edges (G ⊓ K)
  grind

/-!
Since `H ≤ G`, Füredi's theorem contains the edge bound of Turán's theorem.
-/
example [Fintype V] [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1)) :
    #G.edgeFinset ≤ turanNumber (Fintype.card V) r := by
  obtain ⟨H, _, hHG, -, hH⟩ := h.exists_colorable_two_mul_card_edgeFinset_le
  grind [card_le_card (edgeFinset_mono hHG)]

/-!
For example, `turanNumber 10 3 = 33`, so a `4`-clique-free graph on `10` vertices
with `32` edges becomes `3`-colourable after deleting at most one edge.
-/
example [Fintype V] [DecidableRel G.Adj] (hV : Fintype.card V = 10)
    (h : G.CliqueFree 4) (he : #G.edgeFinset = 32) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj), H ≤ G ∧ H.Colorable 3 ∧
      #G.edgeFinset ≤ #H.edgeFinset + 1 := by
  obtain ⟨H, _, hHG, hH, h2⟩ :=
    h.exists_colorable_two_mul_card_edgeFinset_le (r := 3)
  rw [hV, turanNumber_three] at h2
  exact ⟨H, inferInstance, hHG, hH, by grind⟩

/-!
## Andrásfai–Erdős–Sós Theorem

Turán's theorem says that the densest `(r + 1)`-clique-free graphs are Turán graphs,
while Füredi's stability theorem tells us that graphs that are almost extremal, in
terms of number of edges, are almost `r`-colourable.

The Andrásfai–Erdős–Sós theorem gives a different type of stability result related to
the minimum degree: any `(r + 1)`-clique free graph with minimum degree greater than
`(3r − 4)n / (3r − 1)` must be `r`-colourable. For `r = 2` this says that a
triangle-free graph with minimum degree greater than `2n / 5` is bipartite. The
balanced blow-up of `C[5]` shows that `2n / 5` cannot be lowered (see the exercises).

[Figure: The blow-up of $C_5$, an extremal triangle-free graph with $\delta = 2n/5$](https://jt496.github.io/GraphTheoryInLean/figures/blowup_c5.svg)
-/
#check SimpleGraph.colorable_of_cliqueFree_lt_minDegree
-- G.CliqueFree (r + 1) → (3 * r - 4) * n / (3 * r - 1) < δ(G) → G.Colorable r

/-!
For example, if `G` is triangle-free and has an edge, then `mμ[G]` is triangle-free
([Triangle-Free Mycielskians](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-triangle-free-mycielskians))
but not `2`-colourable, since `mμ[G]` is `(k + 1)`-colourable only when `G` is
`k`-colourable
([Colouring Mycielskians](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-colouring-mycielskians)).
So the theorem forces `mμ[G]` to have minimum degree at most `2n / 5`, where
`n = 2 * |V| + 1` is its number of vertices.
-/
example [Fintype V] [DecidableRel G.Adj] (h3 : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) : δ(mμ[G]) ≤ 2 * (2 * Fintype.card V + 1) / 5 := by
  by_contra! h
  have h2 : mμ[G].Colorable 2 :=
    colorable_of_cliqueFree_lt_minDegree (r := 2) h3.mycielskian
      (by simpa [Fintype.card_option, Fintype.card_sum, two_mul] using h)
  obtain ⟨c⟩ := (colorable_mycielskian_succ_iff 1).1 h2
  exact c.valid huv (Subsingleton.elim _ _)

/-!
## Zykov's Theorem *

Turán's theorem bounds the number of edges of an `(r + 1)`-clique-free graph. An edge
is just a `2`-clique, and Zykov proved the following generalization: any
`(r + 1)`-clique-free graph on `n` vertices has at most as many `s`-cliques as the
Turán graph `turanGraph n r`.

For example, the parts of `turanGraph 7 3` have sizes `3`, `2` and `2`, so it has
`3 * 2 * 2 = 12` triangles. Zykov's theorem says that no `4`-clique-free graph on `7`
vertices has more triangles than this.
-/
#eval #((turanGraph 7 3).cliqueFinset 3) -- 12

/-!
Zykov's theorem is unsurprisingly proved by Zykov symmetrization, but it requires a
little more work than in the case of Turán's theorem.

Fix `s`, and write `kₛ(G)` for the number of `s`-cliques of `G` and `dₛ(v)` for the
number of `s`-cliques containing `v`. First we need the analogue of
`card_edgeFinset_replaceVertex_of_not_adj` for cliques.
-/
/--
The `s`-cliques of `G.replaceVertex a b` that do not contain `b` are the `s`-cliques
of `G` that do not contain `b`
-/
lemma isNClique_replaceVertex_iff_of_notMem [DecidableEq V] {a b : V} {s : ℕ}
    {t : Finset V} (hb : b ∉ t) :
    (G.replaceVertex a b).IsNClique s t ↔ G.IsNClique s t := by
  have key : ∀ x ∈ t, ∀ y ∈ t, ((G.replaceVertex a b).Adj x y ↔ G.Adj x y) :=
    fun x hx y hy => adj_replaceVertex_iff_of_ne _ _ (ne_of_mem_of_not_mem hx hb)
      (ne_of_mem_of_not_mem hy hb)
  simp only [isNClique_iff, isClique_iff, Set.Pairwise, mem_coe]
  constructor <;> rintro ⟨h, rfl⟩ <;> refine ⟨fun x hx y hy hxy => ?_, rfl⟩
  · exact (key x hx y hy).1 (h hx hy hxy)
  · exact (key x hx y hy).2 (h hx hy hxy)

/--
The `s`-cliques of `G.replaceVertex a b` containing `b` correspond to the cliques of
`G` that contain `a` but not `b`.
-/
lemma card_filter_mem_cliqueFinset_replaceVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) (s : ℕ) :
    #{t ∈ (G.replaceVertex a b).cliqueFinset s | b ∈ t} =
      #{t ∈ G.cliqueFinset s | a ∈ t ∧ b ∉ t} := by
  refine card_nbij' (fun t => insert a (t.erase b)) (fun t => insert b (t.erase a))
    ?_ ?_ ?_ ?_
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ⊢
    obtain ⟨ht, hbt⟩ := ht
    have hb : b ∉ insert a (t.erase b) := by simp [hab.symm]
    refine ⟨(isNClique_replaceVertex_iff_of_notMem (a := a) hb).1 ?_,
      mem_insert_self _ _, hb⟩
    refine ht.insert_erase (fun w hw => ?_) hbt
    simp only [mem_sdiff, mem_singleton] at hw
    rw [adj_replaceVertex_iff_of_ne_left _ _ hw.2]
    exact (adj_replaceVertex_iff_of_ne_right G a hw.2).1
      (ht.isClique hbt hw.1 (Ne.symm hw.2))
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ⊢
    obtain ⟨ht, hat, hbt⟩ := ht
    refine ⟨?_, mem_insert_self _ _⟩
    refine ((isNClique_replaceVertex_iff_of_notMem hbt).2 ht).insert_erase
      (fun w hw => ?_) hat
    simp only [mem_sdiff, mem_singleton] at hw
    have hwb : w ≠ b := ne_of_mem_of_not_mem hw.1 hbt
    exact (adj_replaceVertex_iff_of_ne_right G a hwb).2
      (ht.isClique hat hw.1 (Ne.symm hw.2))
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht
    have hat : a ∉ t := fun hat =>
      not_adj_replaceVertex_same G a b (ht.1.1 hat ht.2 hab)
    simp [erase_insert (fun h => hat (mem_of_mem_erase h)), insert_erase ht.2]
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht
    simp [erase_insert (fun h => ht.2.2 (mem_of_mem_erase h)), insert_erase ht.2.1]

/--
The number of `s`-cliques in `G.replaceVertex a b` in terms of the number of
`s`-cliques in `G`.
-/
lemma card_cliqueFinset_replaceVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) (s : ℕ) :
    #((G.replaceVertex a b).cliqueFinset s) + #{t ∈ G.cliqueFinset s | b ∈ t} =
      #(G.cliqueFinset s) + #{t ∈ G.cliqueFinset s | a ∈ t ∧ b ∉ t} := by
  have h1 : {t ∈ (G.replaceVertex a b).cliqueFinset s | b ∉ t} =
      {t ∈ G.cliqueFinset s | b ∉ t} := by
    ext t
    simp only [mem_filter, mem_cliqueFinset_iff]
    exact ⟨fun ⟨h, hb⟩ => ⟨(isNClique_replaceVertex_iff_of_notMem hb).1 h, hb⟩,
      fun ⟨h, hb⟩ => ⟨(isNClique_replaceVertex_iff_of_notMem hb).2 h, hb⟩⟩
  have e1 := card_filter_add_card_filter_not
    (s := (G.replaceVertex a b).cliqueFinset s) (b ∈ ·)
  have e2 := card_filter_add_card_filter_not (s := G.cliqueFinset s) (b ∈ ·)
  rw [h1, card_filter_mem_cliqueFinset_replaceVertex hab] at e1
  grind

/--
If `a` and `b` are not adjacent then no clique contains both, `G.replaceVertex a b`
loses the `s`-cliques containing `b` and gains one `s`-clique for each `s`-clique
containing `a`.
-/
lemma card_cliqueFinset_replaceVertex_of_not_adj [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a b : V} (hn : ¬G.Adj a b) (s : ℕ) :
    #((G.replaceVertex a b).cliqueFinset s) + #{t ∈ G.cliqueFinset s | b ∈ t} =
      #(G.cliqueFinset s) + #{t ∈ G.cliqueFinset s | a ∈ t} := by
  by_cases hab : a = b
  · subst hab
    simp
  rw [card_cliqueFinset_replaceVertex hab]
  congr 2
  refine filter_congr fun t ht => ⟨fun h => h.1, fun hat => ⟨hat, fun hbt => ?_⟩⟩
  exact hn ((mem_cliqueFinset_iff.1 ht).1 hat hbt hab)

/--
Call `G` *`s`-clique-maximal* for `r` if it is `(r + 1)`-clique-free and no
`(r + 1)`-clique-free graph on the same vertex set has more `s`-cliques. So
`IsNCliqueMaximal 2 r` is equivalent to `IsTuranMaximal r`.
-/
def IsNCliqueMaximal [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → #(H.cliqueFinset s) ≤ #(G.cliqueFinset s)

namespace IsNCliqueMaximal
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s r : ℕ}

/-!
As in Mathlib's proof of Turán's theorem, performing Zykov symmetrization on a pair
of non-adjacent vertices shows that they lie in the same number of `s`-cliques.
-/
/--
In an `IsNCliqueMaximal s r` graph, non-adjacent vertices lie in the same number of
`s`-cliques.
-/
lemma card_filter_mem_eq_of_not_adj (h : G.IsNCliqueMaximal s r) {a b : V}
    (hn : ¬G.Adj a b) :
    #{t ∈ G.cliqueFinset s | a ∈ t} = #{t ∈ G.cliqueFinset s | b ∈ t} := by
  have kab := card_cliqueFinset_replaceVertex_of_not_adj hn s
  have kba := card_cliqueFinset_replaceVertex_of_not_adj (fun h' => hn h'.symm) s
  have := h.2 _ (h.1.replaceVertex a b)
  have := h.2 _ (h.1.replaceVertex b a)
  grind

end IsNCliqueMaximal

/-!
Now comes the first real difference from the proof for edges (Turán's theorem).
Suppose that `u` and `w` are adjacent, while `v` is adjacent to neither. Symmetrizing
twice, replacing `u` and `w` by copies of `v`, changes the number of `s`-cliques by
`dₛ(v) - dₛ(u) + dₛ(v) - dₛ(w) + dₛ(u, w)`, where `dₛ(u, w)` counts the `s`-cliques
containing both `u` and `w`. Maximality forces `dₛ(u) = dₛ(v) = dₛ(w)`, but
`dₛ(u, w)` can be `0`, so there is no contradiction. Indeed an `s`-clique-maximal
graph need not be complete multipartite: for `s > r` every `(r + 1)`-clique-free
graph has no `s`-cliques, so every one of them is `s`-clique-maximal. (For edges,
`s = 2` and `dₛ(u, w) = 1`, so any `2`-clique-maximal graph is complete multipartite
`IsTuranMaximal.not_adj_trans`.)
-/
/--
The number of `s`-cliques in `(G.replaceVertex v u).replaceVertex v w` in terms of
the number of `s`-cliques in `G`, when the only edge induced by `{u, v, w}` is
`u — w`.
-/
lemma card_cliqueFinset_replaceVertex_replaceVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v w : V} (hvu : ¬G.Adj v u) (hvw : ¬G.Adj v w)
    (huw : G.Adj u w) (s : ℕ) :
    #(((G.replaceVertex v u).replaceVertex v w).cliqueFinset s) +
        #{t ∈ G.cliqueFinset s | u ∈ t} + #{t ∈ G.cliqueFinset s | w ∈ t} =
      #(G.cliqueFinset s) + 2 * #{t ∈ G.cliqueFinset s | v ∈ t} +
        #{t ∈ G.cliqueFinset s | u ∈ t ∧ w ∈ t} := by
  have nvu : v ≠ u := fun e => hvw (e ▸ huw)
  have nuw : u ≠ w := G.ne_of_adj huw
  have hn₁ : ¬(G.replaceVertex v u).Adj v w :=
    (G.adj_replaceVertex_iff_of_ne v nvu nuw.symm).not.mpr hvw
  have hv : {t ∈ (G.replaceVertex v u).cliqueFinset s | v ∈ t} =
      {t ∈ G.cliqueFinset s | v ∈ t} := by
    ext t
    simp only [mem_filter, mem_cliqueFinset_iff, and_congr_left_iff]
    intro hvt
    by_cases hut : u ∈ t
    · constructor <;> intro ht
      · exact absurd (ht.1 hvt hut nvu) (not_adj_replaceVertex_same G v u)
      · exact absurd (ht.1 hvt hut nvu) hvu
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
    simp only [and_comm]
  have k₁ := card_cliqueFinset_replaceVertex_of_not_adj hvu s
  have k₂ := card_cliqueFinset_replaceVertex_of_not_adj hn₁ s
  rw [hv, hw] at k₂
  grind

/-!
So how do we fix this argument? The problem is caused by the presence of edges that
lie in no `s`-clique. Deleting all such edges does not change the number of
`s`-cliques, and will yield a subgraph that we can prove is complete multipartite.

We do this by forming the graph `G.cliqueUnion s` which is the union of all the
`s`-cliques of `G`.
-/
/-- The union of the `s`-cliques of `G`: distinct vertices are adjacent iff they lie
in a common `s`-clique of `G`. -/
def cliqueUnion (G : SimpleGraph V) (s : ℕ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ t, G.IsNClique s t ∧ x ∈ t ∧ y ∈ t

@[simp]
lemma cliqueUnion_adj {s : ℕ} {x y : V} :
    (G.cliqueUnion s).Adj x y ↔ x ≠ y ∧ ∃ t, G.IsNClique s t ∧ x ∈ t ∧ y ∈ t :=
  Iff.rfl

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s : ℕ} :
    DecidableRel (G.cliqueUnion s).Adj := fun x y =>
  decidable_of_iff (x ≠ y ∧ ∃ t ∈ G.cliqueFinset s, x ∈ t ∧ y ∈ t) (by simp)
/--
The union of the `s`-cliques of `G` is a subgraph of `G`.
-/
lemma cliqueUnion_le (s : ℕ) : G.cliqueUnion s ≤ G :=
  fun _ _ ⟨hxy, _, ht, hx, hy⟩ => ht.1 hx hy hxy

/--
The `s`-cliques of `G.cliqueUnion s` are the same as the `s`-cliques of `G`.
-/
lemma isNClique_cliqueUnion_iff {s : ℕ} {t : Finset V} :
    (G.cliqueUnion s).IsNClique s t ↔ G.IsNClique s t :=
  ⟨fun ht => ht.mono (G.cliqueUnion_le s),
    fun ht => ⟨fun _ hx _ hy hxy => ⟨hxy, t, ht, hx, hy⟩, ht.2⟩⟩

/--
The finite set of `s`-cliques of `G.cliqueUnion s` is the same as the finite set of
`s`-cliques
-/
lemma cliqueFinset_cliqueUnion [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (s : ℕ) : (G.cliqueUnion s).cliqueFinset s = G.cliqueFinset s := by
  ext t
  simp [isNClique_cliqueUnion_iff]

/--
Every edge of `G.cliqueUnion s` lies in an `s`-clique of `G.cliqueUnion s`.
-/
lemma cliqueUnion_cliqueUnion (s : ℕ) :
    (G.cliqueUnion s).cliqueUnion s = G.cliqueUnion s := by
  ext
  simp [isNClique_cliqueUnion_iff]

namespace IsNCliqueMaximal

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s r : ℕ}

/-!
Our next lemma looks a little odd mathematically. The hypothesis
`G ≤ G.cliqueUnion s` should be read as "every edge of `G` lies in an `s`-clique".
(Obviously we also have `G.cliqueUnion s ≤ G` so in fact `G = G.cliqueUnion s`.)
-/
/--
If every edge of `G` lies in an `s`-clique, then `G` is complete multipartite.
-/
lemma isCompleteMultipartite_of_le_cliqueUnion (h : G.IsNCliqueMaximal s r)
    (hG : G ≤ G.cliqueUnion s) : G.IsCompleteMultipartite := by
  constructor
  intro u v w huv hvw huw
  have hvu : ¬G.Adj v u := fun h' => huv h'.symm
  have hk := card_cliqueFinset_replaceVertex_replaceVertex hvu hvw huw s
  have := h.card_filter_mem_eq_of_not_adj hvu
  have := h.card_filter_mem_eq_of_not_adj hvw
  have := h.2 _ ((h.1.replaceVertex v u).replaceVertex v w)
  -- the edge `uw` lies in an `s`-clique
  obtain ⟨-, t, ht, hut, hwt⟩ := hG huw
  have : 0 < #{t ∈ G.cliqueFinset s | u ∈ t ∧ w ∈ t} :=
    card_pos.2 ⟨t, mem_filter.2 ⟨mem_cliqueFinset_iff.2 ht, hut, hwt⟩⟩
  grind

end IsNCliqueMaximal

/-!
The next key observation is that a complete multipartite graph with one `s`-clique
has many. Let `t` be an `s`-clique and let `x` and `y` be adjacent. At most one
vertex of `t` is not adjacent to `x`, since two such vertices would both lie in the
part of `x`, and similarly for `y`. So at least `s - 2` vertices of `t` are adjacent
to both `x` and `y`, and together with `x` and `y` they form an `s`-clique. We allow
the edge `x — y` to come from a larger graph `H`.
-/
/--
If `G` is complete multipartite and has an `s`-clique, then every edge of a graph
`H` containing `G` lies in an `s`-clique of `H`.
-/
lemma IsCompleteMultipartite.exists_isNClique_of_le (hc : G.IsCompleteMultipartite)
    {H : SimpleGraph V} (hGH : G ≤ H) {s : ℕ} (hs : 2 ≤ s) {t : Finset V}
    (ht : G.IsNClique s t) {x y : V} (hxy : H.Adj x y) :
    ∃ u, H.IsNClique s u ∧ x ∈ u ∧ y ∈ u := by
  classical
  -- at most one vertex of `t` is not adjacent to a given vertex `z`
  have hle (z : V) : #{a ∈ t | ¬G.Adj z a} ≤ 1 := by
    refine card_le_one.2 fun a ha b hb => ?_
    rw [mem_filter] at ha hb
    by_contra hab
    exact hc.trans _ _ _ (fun h => ha.2 h.symm) hb.2 (ht.1 ha.1 hb.1 hab)
  have hcard : s - 2 ≤ #{a ∈ t | G.Adj x a ∧ G.Adj y a} := by
    have hsub : t ⊆ ({a ∈ t | G.Adj x a ∧ G.Adj y a} ∪ {a ∈ t | ¬G.Adj x a}) ∪
        {a ∈ t | ¬G.Adj y a} := by
      intro a ha
      simp only [mem_union, mem_filter]
      tauto
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    have := hle x
    have := hle y
    have := ht.2
    grind
  obtain ⟨u, hu, hu2⟩ := exists_subset_card_eq hcard
  have hxyu (a) (ha : a ∈ u) : G.Adj x a ∧ G.Adj y a := (mem_filter.1 (hu ha)).2
  have hu' : H.IsNClique (s - 2) u :=
    ⟨(ht.1.subset (coe_subset.2 (hu.trans (filter_subset _ _)))).mono hGH, hu2⟩
  have hyu := hu'.insert fun b hb => hGH (hxyu b hb).2
  have hxu := hyu.insert (a := x) fun b hb => by
    rcases mem_insert.1 hb with rfl | hb
    · exact hxy
    · exact hGH (hxyu b hb).1
  have e : s - 2 + 1 + 1 = s := by grind
  rw [e] at hxu
  exact ⟨_, hxu, mem_insert_self _ _, mem_insert_of_mem (mem_insert_self _ _)⟩

namespace IsNCliqueMaximal
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s r : ℕ}

/-!
Now let `G` be `s`-clique-maximal with at least one `s`-clique. Then
`G.cliqueUnion s` is `s`-clique-maximal too, and every edge of it lies in an
`s`-clique, so it is complete multipartite. Applying the key lemma to it, with
`H = G`, shows that every edge of `G` lies in an `s`-clique, so `G` is complete
multipartite as well.
-/
/--
Any `IsNCliqueMaximal s r` graph with at least one `s`-clique is complete
multipartite (for `s ≥ 2`).
-/
lemma isCompleteMultipartite (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s)
    {t : Finset V} (ht : G.IsNClique s t) : G.IsCompleteMultipartite := by
  have h₀ : (G.cliqueUnion s).IsNCliqueMaximal s r := by
    refine ⟨h.1.anti (G.cliqueUnion_le s), fun H _ hH => ?_⟩
    rw [cliqueFinset_cliqueUnion]
    exact h.2 H hH
  have hc₀ :=
    h₀.isCompleteMultipartite_of_le_cliqueUnion (cliqueUnion_cliqueUnion s).ge
  refine h.isCompleteMultipartite_of_le_cliqueUnion fun x y hxy => ?_
  obtain ⟨u, hu, hx, hy⟩ := hc₀.exists_isNClique_of_le (G.cliqueUnion_le s) hs
    (isNClique_cliqueUnion_iff.2 ht) hxy
  exact ⟨hxy.ne, u, hu, hx, hy⟩

end IsNCliqueMaximal

/-!
The Turán graph `turanGraph n r` is not just complete multipartite, it is also
balanced. For general `s`-cliques the "balancing of parts" argument is rather more
involved.

Suppose that `G` is an unbalanced complete multipartite graph. Let `A` and `B` be
parts with `#B + 1 < #A`, and move a vertex `w ∈ A` to `B`: this is
`G.replaceVertex v w` for any `v ∈ B`. For edges the change is a difference of
degrees. For cliques it is `(#A - #B - 1)` times the number of `(s - 2)`-cliques in
the remaining parts. Since `G` is only maximal for the number of `s`-cliques, a
change of `0` gives no contradiction, so we need this change to be strictly positive.

Since the parts are unbalanced, `A` has at least `#B + 2` vertices, so we can fix a
vertex `a ∈ A` other than `w`. We now map `B` injectively into `A \ {w, a}` using
some `φ`. We then extend `φ` to a map `σ : V → V` that sends `w` to `v`, and fixes
every other vertex.

Let `t` be an `s`-clique containing `w`. It has no other vertex in `A`, and at most
one vertex in `B`, so `σ` moves `w` into `B` and the vertex of `t` in `B` (if any)
into `A`, and fixes the rest. Hence `t.image σ` is again an `s`-clique, by
`IsNClique.image_of_adj` from
[Cliques](https://jt496.github.io/GraphTheoryInLean/Cliques/#chapter-cliques). It
contains `v` but neither `w` nor `a`, and `σ` is injective on the vertices that can
lie in such a clique (`w` and the vertices outside `A`). So `t ↦ t.image σ` is an
injection from the `s`-cliques containing `w` to those containing `v` that avoid `w`
and `a`: this is the inequality below. Avoiding `a` is exactly what we need in
`card_le_card_add_one`, where we find an `s`-clique containing `v` and `a`. It avoids
`w`, so it is missed by the injection, and so the change is strictly positive.
-/
lemma IsCompleteMultipartite.card_filter_mem_cliqueFinset_le [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hc : G.IsCompleteMultipartite) {v w a : V}
    (hvw : G.Adj v w) (hwa : ¬G.Adj w a) (haw : a ≠ w)
    (hlt : #{x | ¬G.Adj v x} + 1 < #{x | ¬G.Adj w x}) (s : ℕ) :
    #{t ∈ G.cliqueFinset s | w ∈ t} ≤
      #{t ∈ G.cliqueFinset s | v ∈ t ∧ w ∉ t ∧ a ∉ t} := by
  set A : Finset V := {x | ¬G.Adj w x}
  set B : Finset V := {x | ¬G.Adj v x}
  have nt {x y z : V} (h₁ : ¬G.Adj x y) (h₂ : ¬G.Adj y z) : ¬G.Adj x z :=
    hc.trans _ _ _ h₁ h₂
  have hA {x : V} : x ∈ A ↔ ¬G.Adj w x := by simp [A]
  have hB {x : V} : x ∈ B ↔ ¬G.Adj v x := by simp [B]
  have hwA : w ∈ A := hA.2 (G.irrefl)
  have hvA : v ∉ A := fun h => hA.1 h hvw.symm
  have hvB : v ∈ B := hB.2 (G.irrefl)
  have hwB : w ∉ B := fun h => hB.1 h hvw
  have haA : a ∈ A := hA.2 hwa
  -- every vertex of `A` is adjacent to every vertex of `B`
  have hAB {x y : V} (hx : x ∈ A) (hy : y ∈ B) : G.Adj x y := by
    by_contra hxy
    exact nt (nt (hA.1 hx) hxy) (fun h => hB.1 hy h.symm) hvw.symm
  -- an injection `φ` from `B` to `A \ {w, a}`
  have hcard : Fintype.card B ≤ Fintype.card ((A.erase w).erase a) := by
    simp only [Fintype.card_coe, card_erase_of_mem (mem_erase.2 ⟨haw, haA⟩),
      card_erase_of_mem hwA]
    grind
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hφw (x : B) : (φ x : V) ∈ A.erase w := mem_of_mem_erase (φ x).2
  have hφA (x : B) : (φ x : V) ∈ A := mem_of_mem_erase (hφw x)
  let σ : V → V := fun x => if x = w then v else if hx : x ∈ B then φ ⟨x, hx⟩ else x
  -- the cliques containing `w` lie in `{w} ∪ Aᶜ`
  have hsub {t : Finset V} (ht : G.IsNClique s t) (hwt : w ∈ t) :
      (t : Set V) ⊆ {x | x = w ∨ x ∉ A} := fun x hx => by
    by_cases hxw : x = w
    · exact .inl hxw
    · exact .inr fun hxA => hA.1 hxA (ht.1 hwt hx (Ne.symm hxw))
  -- `σ` on the vertices that can lie in a clique containing `w`
  have hσ {x : V} (hx : x = w ∨ x ∉ A) :
      (x = w ∧ σ x = v) ∨ (∃ hxB : x ∈ B, σ x = φ ⟨x, hxB⟩) ∨
        (x ∉ A ∧ x ∉ B ∧ σ x = x) := by
    by_cases hxw : x = w
    · exact .inl ⟨hxw, by simp [σ, hxw]⟩
    · grind
  have hinj : Set.InjOn σ {x | x = w ∨ x ∉ A} := by
    intro x hx y hy hxy
    rcases hσ hx with ⟨hxw, hx'⟩ | ⟨hxB, hx'⟩ | ⟨hxA, hxB, hx'⟩ <;>
      rcases hσ hy with ⟨hyw, hy'⟩ | ⟨hyB, hy'⟩ | ⟨hyA, hyB, hy'⟩ <;>
      rw [hx', hy'] at hxy <;> try grind
    · exact congrArg Subtype.val (φ.injective (Subtype.ext hxy))
  have hadj {x y : V} (hx : x = w ∨ x ∉ A) (hy : y = w ∨ y ∉ A) (hxy : G.Adj x y) :
      G.Adj (σ x) (σ y) := by
    rcases hσ hx with ⟨hxw, hx'⟩ | ⟨hxB, hx'⟩ | ⟨hxA, hxB, hx'⟩ <;>
      rcases hσ hy with ⟨hyw, hy'⟩ | ⟨hyB, hy'⟩ | ⟨hyA, hyB, hy'⟩ <;>
      rw [hx', hy'] <;> try grind
    · exact absurd hxy (nt (fun h => hB.1 hxB h.symm) (hB.1 hyB))
    · exact not_not.1 fun h => hxB (hB.2 fun h' => h h'.symm)
    · exact not_not.1 fun h => hxA (hA.2 (nt (hA.1 (hφA _)) fun h' => h h'.symm))
  refine card_le_card_of_injOn (fun t => t.image σ) (fun t ht => ?_)
    (fun t ht t' ht' htt' => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ⊢
    obtain ⟨ht, hwt⟩ := ht
    refine ⟨ht.image_of_adj (hinj.mono (hsub ht hwt)) fun x hx y hy =>
        hadj (hsub ht hwt hx) (hsub ht hwt hy), mem_image.2 ⟨w, hwt, by simp [σ]⟩,
      fun hw => ?_, fun ha => ?_⟩
    · obtain ⟨x, hx, hxw⟩ := mem_image.1 hw
      rcases hσ (hsub ht hwt hx) with ⟨-, hx'⟩ | ⟨hxB, hx'⟩ | ⟨hxA, -, hx'⟩
        <;> grind
    · obtain ⟨x, hx, hxa⟩ := mem_image.1 ha
      rcases hσ (hsub ht hwt hx) with ⟨-, hx'⟩ | ⟨hxB, hx'⟩ | ⟨hxA, -, hx'⟩
        <;> grind
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_cliqueFinset_iff] at ht ht' htt'
    apply Finset.coe_injective
    exact (hinj.image_eq_image_iff
      (hsub ht.1 ht.2) (hsub ht'.1 ht'.2)).1
        (by exact_mod_cast htt')

/--
Vertices whose parts have different sizes lie in different parts and so are adjacent.
-/
lemma IsCompleteMultipartite.adj_of_card_ne [Fintype V] [DecidableRel G.Adj]
    (hc : G.IsCompleteMultipartite) {v w : V}
    (hne : #{x | ¬G.Adj v x} ≠ #{x | ¬G.Adj w x}) : G.Adj v w := by
  by_contra hn
  refine hne (congrArg card ?_)
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hc.trans _ _ _ fun h' => hn h'.symm, hc.trans _ _ _ hn⟩

namespace IsNCliqueMaximal
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s r : ℕ}
/--
An `s`-clique-maximal graph with at least one `s`-clique has degrees that differ by
at most one.
-/
lemma card_le_card_add_one (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s)
    {t : Finset V} (ht : G.IsNClique s t) (v w : V) :
    #{x | ¬G.Adj w x} ≤ #{x | ¬G.Adj v x} + 1 := by
  by_contra! hlt
  have hc := h.isCompleteMultipartite hs ht
  have hvw := hc.adj_of_card_ne (v := v) (w := w) (by grind)
  obtain ⟨a, ha, haw⟩ := exists_mem_ne (s := {x | ¬G.Adj w x}) (by grind) w
  have hwa : ¬G.Adj w a := (mem_filter.1 ha).2
  -- some `s`-clique contains `v` and `a`, and hence not `w`
  have hva : G.Adj v a := not_not.1 fun hva => hc.trans _ _ _ hwa
    (fun h' => hva h'.symm) hvw.symm
  obtain ⟨u, hu, hvu, hau⟩ := hc.exists_isNClique_of_le le_rfl hs ht hva
  have hwu : w ∉ u := fun hwu => hwa (hu.1 hwu hau haw.symm)
  have hd := hc.card_filter_mem_cliqueFinset_le hvw hwa haw hlt s
  have hd' : #{t ∈ G.cliqueFinset s | v ∈ t ∧ w ∉ t ∧ a ∉ t} <
      #{t ∈ G.cliqueFinset s | v ∈ t ∧ w ∉ t} :=
    card_lt_card <| (ssubset_iff_of_subset
      (monotone_filter_right _ fun _ _ ht => ⟨ht.1, ht.2.1⟩)).2
        ⟨u, by simp [hu, hvu, hwu], by simp [hau]⟩
  have hk := card_cliqueFinset_replaceVertex (G := G) hvw.ne s
  have := h.2 _ (h.1.replaceVertex v w)
  grind

/--
Any `s`-clique-maximal graph with at least one `s`-clique is either complete or
contains an `r`-clique.
-/
lemma not_cliqueFree_of_not_adj (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s)
    {t : Finset V} (ht : G.IsNClique s t) {x y : V} (hxy : x ≠ y) (hn : ¬G.Adj x y) :
    ¬G.CliqueFree r := fun hcf => by
  have hxy' : (G ⊔ edge x y).Adj x y := by simp [edge_adj, hxy]
  obtain ⟨u, hu, hxu, hyu⟩ :=
    (h.isCompleteMultipartite hs ht).exists_isNClique_of_le le_sup_left hs ht hxy'
  have hlt : G.cliqueFinset s ⊂ (G ⊔ edge x y).cliqueFinset s :=
    (ssubset_iff_of_subset (cliqueFinset_mono _ le_sup_left)).2
      ⟨u, mem_cliqueFinset_iff.2 hu,
        fun hu' => hn ((mem_cliqueFinset_iff.1 hu').1 hxu hyu hxy)⟩
  exact (card_lt_card hlt).not_ge (h.2 _ (hcf.sup_edge x y))

end IsNCliqueMaximal

#check IsTuranMaximal.nonempty_iso_turanGraph
/-!
The rest of the argument follows the Mathlib proof of Turán's theorem closely.
Mathlib proves that a Turán-maximal graph is isomorphic to the Turán graph
(`IsTuranMaximal.nonempty_iso_turanGraph`) through a series of lemmas about its
parts, such as `IsTuranMaximal.card_parts`. These assume Turán-maximality, so we
cannot apply them. Instead we prove the same lemmas for complete multipartite graphs,
assuming in turn the three properties of `s`-clique-maximal graphs established above.
-/
namespace IsCompleteMultipartite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (hc : G.IsCompleteMultipartite)

instance : DecidableRel hc.setoid.r := inferInstanceAs (DecidableRel (¬G.Adj · ·))

/-- The parts of a finite complete multipartite graph, as a `Finpartition` of its
vertices. -/
def finpartition : Finpartition (univ : Finset V) := Finpartition.ofSetoid hc.setoid

/-- Two vertices are non-adjacent iff they lie in the same part. -/
lemma not_adj_iff_part_eq {s t : V} :
    ¬G.Adj s t ↔ hc.finpartition.part s = hc.finpartition.part t := by
  change hc.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change t ∈ hc.finpartition.part s ↔ _
  rw [hc.finpartition.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s), eq_comm]

/-- The part of `v` consists of the non-neighbours of `v`. -/
lemma part_finpartition (v : V) :
    hc.finpartition.part v = ({x | ¬G.Adj v x} : Finset V) := by
  ext x
  rw [mem_filter, finpartition, Finpartition.mem_part_ofSetoid_iff_rel]
  simp only [mem_univ, true_and]
  rfl

/-- If the parts differ in size by at most one, they form an equipartition. -/
lemma isEquipartition (hbal : ∀ v w, #{x | ¬G.Adj w x} ≤ #{x | ¬G.Adj v x} + 1) :
    hc.finpartition.IsEquipartition := by
  intro large small hl hs
  obtain ⟨w, hw⟩ := hc.finpartition.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := hc.finpartition.nonempty_of_mem_parts hs
  rw [← hc.finpartition.part_eq_of_mem hl hw, ← hc.finpartition.part_eq_of_mem hs hv,
    part_finpartition, part_finpartition]
  exact hbal v w

/-- An `(r + 1)`-clique-free complete multipartite graph has at most `r` parts, since
one vertex from each part gives a clique. -/
lemma card_parts_le {r : ℕ} (hcf : G.CliqueFree (r + 1)) :
    #hc.finpartition.parts ≤ r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := hc.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ ?_, rfl⟩
    contrapose hn
    exact hz.injOn hv hw (by rwa [← hc.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (hcf.mono (Nat.succ_le_of_lt l)) ncf

/-- If `G` has an `r`-clique as soon as two distinct vertices are non-adjacent, then
it has exactly `min n r` parts, where `n` is the number of vertices. -/
lemma card_parts {r : ℕ} (hcf : G.CliqueFree (r + 1))
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
  have hinj : Set.InjOn hc.finpartition.part (z : Set V) := by
    intro a ha b hb hab
    by_contra hne
    exact (hc.not_adj_iff_part_eq.2 hab) (hz.1 ha hb hne)
  have hsize : #z ≤ #hc.finpartition.parts :=
    card_le_card_of_injOn hc.finpartition.part
      (fun a _ => hc.finpartition.part_mem.2 (mem_univ a)) hinj
  exact (Nat.not_le_of_gt l.2) (hz.card_eq ▸ hsize)

end IsCompleteMultipartite

/-- A complete multipartite `(r + 1)`-clique-free graph whose parts differ in size by
at most one, and which has an `r`-clique as soon as two distinct vertices are
non-adjacent, is isomorphic to the Turán graph. -/
theorem IsCompleteMultipartite.nonempty_iso_turanGraph [Fintype V]
    [DecidableRel G.Adj] {r : ℕ} (hc : G.IsCompleteMultipartite)
    (hcf : G.CliqueFree (r + 1))
    (hbal : ∀ v w, #{x | ¬G.Adj w x} ≤ #{x | ¬G.Adj v x} + 1)
    (hsat : ∀ x y, x ≠ y → ¬G.Adj x y → ¬G.CliqueFree r) :
    Nonempty (G ≃g turanGraph (Fintype.card V) r) := by
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

namespace IsNCliqueMaximal

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {s r : ℕ}

/-- For `2 ≤ s`, an `s`-clique-maximal graph with an `s`-clique is a Turán graph. -/
theorem nonempty_iso_turanGraph (h : G.IsNCliqueMaximal s r) (hs : 2 ≤ s)
    {t : Finset V} (ht : G.IsNClique s t) :
    Nonempty (G ≃g turanGraph (Fintype.card V) r) :=
  (h.isCompleteMultipartite hs ht).nonempty_iso_turanGraph h.1
    (h.card_le_card_add_one hs ht) fun _ _ => h.not_cliqueFree_of_not_adj hs ht

end IsNCliqueMaximal

/-!
Zykov's theorem follows. Maximizing the number of `s`-cliques over the finitely many
`(r + 1)`-clique-free graphs on `V` gives an `s`-clique-maximal graph `H`, and `G`
itself shows that there is at least one candidate. If `H` has no `s`-clique then
neither does `G`. Otherwise `H` is a Turán graph, and `G` has at most as many
`s`-cliques as `H`. This needs `2 ≤ s`. For `s ≤ 1` every set of `s` vertices is a
clique, so the `s`-cliques do not depend on the graph.
-/
/-- For `s ≤ 1` all graphs on `V` have the same `s`-cliques. -/
lemma cliqueFinset_eq_of_le_one [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {H : SimpleGraph V} [DecidableRel H.Adj] {s : ℕ} (hs : s ≤ 1) :
    G.cliqueFinset s = H.cliqueFinset s := by
  interval_cases s <;> ext <;> simp [isNClique_zero, isNClique_one]

/-- Isomorphic graphs have the same number of `s`-cliques. -/
lemma Iso.card_cliqueFinset_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (e : G ≃g H) (s : ℕ) : #(G.cliqueFinset s) = #(H.cliqueFinset s) := by
  refine card_nbij' (fun t => t.image e) (fun t => t.image e.symm) (fun t ht => ?_)
    (fun t ht => ?_) (fun t _ => ?_) (fun t _ => ?_)
  · rw [mem_coe, mem_cliqueFinset_iff] at ht ⊢
    exact ht.mapHom e.toHom
  · rw [mem_coe, mem_cliqueFinset_iff] at ht ⊢
    exact ht.mapHom e.symm.toHom
  all_goals simp [image_image, Function.comp_def]

/-- **Zykov's theorem**: an `(r + 1)`-clique-free graph on `n` vertices has at most
as many `s`-cliques as the Turán graph `turanGraph n r`. -/
theorem CliqueFree.card_cliqueFinset_le [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {r : ℕ} (h : G.CliqueFree (r + 1)) (s : ℕ) :
    #(G.cliqueFinset s) ≤ #((turanGraph (Fintype.card V) r).cliqueFinset s) := by
  rcases lt_or_ge s 2 with hs | hs
  · -- for `s ≤ 1` compare the empty graphs on `V` and `Fin (card V)`
    let e : (⊥ : SimpleGraph V) ≃g (⊥ : SimpleGraph (Fin (Fintype.card V))) :=
      { toEquiv := Fintype.equivFin V, map_rel_iff' := by simp }
    rw [cliqueFinset_eq_of_le_one (H := ⊥) (by grind),
      cliqueFinset_eq_of_le_one (G := turanGraph _ r) (H := ⊥) (by grind)]
    exact (e.card_cliqueFinset_eq s).le
  classical
  -- an `s`-clique-maximal graph `H`; `G` itself is a candidate
  obtain ⟨H, hH, hmax⟩ :=
    ({H | H.CliqueFree (r + 1)} : Finset (SimpleGraph V)).exists_max_image
      (fun H => #(H.cliqueFinset s)) ⟨G, by simpa using h⟩
  have hH' : H.IsNCliqueMaximal s r :=
    ⟨by simpa using hH, fun H' _ hH' => by convert hmax H' (by simpa using hH')⟩
  have hGH := hH'.2 G h
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
Turán's theorem also says that the Turán graph is the *only* extremal graph. The same
is true for Zykov's theorem when `2 ≤ s ≤ r` and `s ≤ n`. The other cases are
degenerate: for `s ≤ 1` all graphs on `n` vertices have the same number of
`s`-cliques, and for `s > r` or `s > n` no `(r + 1)`-clique-free graph has any.

When `s ≤ r` and `s ≤ n`, the vertices `0, …, s - 1` of the Turán graph lie in
different parts, so it has an `s`-clique. A graph with as many `s`-cliques as the
Turán graph is `s`-clique-maximal by Zykov's theorem, so it has an `s`-clique too,
and it is a Turán graph.
-/
theorem CliqueFree.card_cliqueFinset_eq_iff_nonempty_iso_turanGraph [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r s : ℕ} (h : G.CliqueFree (r + 1))
    (hs : 2 ≤ s) (hsr : s ≤ r) (hsn : s ≤ Fintype.card V) :
    #(G.cliqueFinset s) = #((turanGraph (Fintype.card V) r).cliqueFinset s) ↔
      Nonempty (G ≃g turanGraph (Fintype.card V) r) := by
  refine ⟨fun hk => ?_, fun ⟨e⟩ => e.card_cliqueFinset_eq s⟩
  have hT : (turanGraph (Fintype.card V) r).IsNClique s
      (univ.map (Fin.castLEEmb hsn)) := by
    refine ⟨?_, by simp⟩
    simp only [coe_map, coe_univ, Set.image_univ]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [turanGraph_adj]
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    rw [Nat.mod_eq_of_lt (i.isLt.trans_le hsr),
      Nat.mod_eq_of_lt (j.isLt.trans_le hsr)]
    exact fun e => hij (Fin.ext e)
  obtain ⟨t, ht⟩ : (G.cliqueFinset s).Nonempty := by
    rw [← card_pos, hk]
    exact card_pos.2 ⟨_, mem_cliqueFinset_iff.2 hT⟩
  exact IsNCliqueMaximal.nonempty_iso_turanGraph
    ⟨h, fun H _ hH => (hH.card_cliqueFinset_le s).trans hk.ge⟩ hs
    (mem_cliqueFinset_iff.1 ht)

/-!
So a `4`-clique-free graph on `7` vertices with `12` triangles is isomorphic to
`turanGraph 7 3`.
-/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hV : Fintype.card V = 7)
    (h : G.CliqueFree 4) (h12 : #(G.cliqueFinset 3) = 12) :
    Nonempty (G ≃g turanGraph 7 3) := by
  have := (h.card_cliqueFinset_eq_iff_nonempty_iso_turanGraph (r := 3) (s := 3)
    (by grind) le_rfl (by grind)).1 (by rw [h12, hV]; decide)
  rwa [hV] at this

/-!
# Extremal Numbers

Turán's theorem answers the extremal question for complete graphs. For a general
forbidden graph `H`, the *extremal number* `extremalNumber n H` is the maximum number
of edges in an `H`-free graph on `n` vertices. Recall that `H.Free G` means that `G`
contains no copy of `H`
([Copies](https://jt496.github.io/GraphTheoryInLean/Maps/#section-copies)). Mathlib
defines it as a supremum over all graphs on `Fin n`.
-/
#source extremalNumber

/-!
Although this is a maximum over a finite set, `extremalNumber` is `noncomputable`:
`H.Free G` is not decidable in general, and the definition uses classical
`Finset.filter` and edge sets. So `#eval extremalNumber 4 K[3]` fails, and we must
reason about extremal numbers instead. The basic tools are the following.
-/
#check card_edgeFinset_le_extremalNumber
-- H.Free G → #G.edgeFinset ≤ extremalNumber (Fintype.card V) H

#check IsContained.of_extremalNumber_lt_card_edgeFinset
-- extremalNumber (Fintype.card V) H < #G.edgeFinset → H ⊑ G

#check extremalNumber_le_iff
-- extremalNumber (card V) H ≤ m ↔ every H-free graph on V has at most m edges

/-!
Turán's theorem, restated in this language, computes the extremal numbers of
complete graphs. Here `α` is any finite type with at least two elements, so
`(⊤ : SimpleGraph α)` is a complete graph on `card α` vertices.
-/
#check extremalNumber_top
-- extremalNumber n (⊤ : SimpleGraph α) = #(turanGraph n (card α - 1)).edgeFinset

#check card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph
-- G is ⊤-free with the most edges ↔ G ≃g turanGraph (card V) (card α - 1)

/-!
For bipartite forbidden graphs the extremal numbers are much smaller. The
*Zarankiewicz function* `zarankiewicz m n s t` is the maximum number of edges in a
`K[s, t]`-free bipartite graph with parts of sizes `m` and `n`, and it is closely
related to `extremalNumber n K[s, t]`.
-/
#check zarankiewicz_le_extremalNumber
-- zarankiewicz m n s t ≤ extremalNumber (m + n) (completeBipartiteGraph α β)

/-!
The main upper bound for these numbers, the Kővári–Sós–Turán theorem
`extremalNumber n K[s, t] = O(n^(2 - 1/s))`, is not yet in Mathlib.

## Turán Density and the Erdős–Stone Theorem *

How does `extremalNumber n H` grow with `n`? Dividing by the number `n.choose 2` of
possible edges gives a sequence that is decreasing (for `n ≥ 2`), so it converges.
Its limit is the *Turán density* `turanDensity H`. Statements about limits in Mathlib
use filters: `Tendsto f atTop (𝓝 a)` says that `f n → a` as `n → ∞`.
-/
#source turanDensity

#check tendsto_turanDensity
-- extremalNumber n H / n.choose 2 tends to turanDensity H as n → ∞

/-!
So `extremalNumber n H` is asymptotically `turanDensity H * n.choose 2`, which
Mathlib writes with `~[atTop]` (asymptotic equivalence) when the density is nonzero.
-/
#check isEquivalent_extremalNumber
-- turanDensity H ≠ 0 → extremalNumber n H ~ turanDensity H * n.choose 2

/-!
Phrases like "for all sufficiently large `n`" are written with `∀ᶠ n in atTop`. For
example, for any `ε > 0`, every large enough graph with at least
`(turanDensity H + ε) * n.choose 2` edges contains a copy of `H`.
-/
#check eventually_isContained_of_card_edgeFinset
-- ∀ᶠ n in atTop, #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 → H ⊑ G

/-!
The *Erdős–Stone theorem* says that a large graph whose density is a little above the
Turán density of `K[r + 1]` contains not just `K[r + 1]` but a complete
`(r + 1)`-partite graph `completeEquipartiteGraph (r + 1) t` with large parts.
Mathlib has the minimum degree version of this theorem.
-/
#check eventually_completeEquipartiteGraph_isContained_of_minDegree
-- ∀ᶠ n in atTop, δ(G) ≥ (1 - 1/r + ε) n → completeEquipartiteGraph (r + 1) t ⊑ G

/-!
The Erdős–Stone–Simonovits formula `turanDensity H = 1 - 1 / (χ H - 1)` that follows
from this is not yet in Mathlib.

# Regularity and Removal *

This section surveys some deep results of Mathlib's extremal graph theory library:
the Szemerédi regularity lemma, the triangle removal lemma and their application to
additive combinatorics. Their statements use real numbers and finite partitions
rather than the graph-theoretic language of the earlier chapters.

## Edge Density and Uniform Pairs

The *edge density* between two finite sets `s` and `t` of vertices is the fraction of
pairs in `s ×ˢ t` that are edges. It is a rational number, so we can compute it.
-/
#check edgeDensity_def -- G.edgeDensity s t = #(G.interedges s t) / (#s * #t)

#eval C[6].edgeDensity {0, 2, 4} {1, 3, 5} -- 2 / 3

/-!
A pair `(s, t)` is `ε`-*uniform* if the edges between them are spread evenly: any
`s' ⊆ s` and `t' ⊆ t` containing at least an `ε` fraction of `s` and `t` have edge
density within `ε` of the density between `s` and `t`. This mimics a random
bipartite graph.
-/
#source IsUniform

/-!
## The Szemerédi Regularity Lemma

The *regularity lemma* says that every graph can be approximated by a structured
one: its vertices can be partitioned into a bounded number of nearly equal parts so
that most pairs of parts are `ε`-uniform.

[Figure: Vertices partitioned into equal-sized blocks with pair densities](https://jt496.github.io/GraphTheoryInLean/figures/szemeredi.svg)

In Mathlib's statement, `P.IsEquipartition` says the parts of `P` differ in size by
at most `1`, and `P.IsUniform G ε` says that at most an `ε` fraction of the pairs of
parts are not `ε`-uniform. The number of parts is at least a chosen `l` and at most
`bound ε l`, which crucially depends only on `ε` and `l`, not on the graph.
-/
#check szemeredi_regularity
-- ∃ equipartition P with l ≤ #P.parts ≤ bound ε l and P.IsUniform G ε

/-!
## The Triangle Removal Lemma

Any graph can be made `H`-free by deleting one edge from each copy of `H`. Mathlib
calls the result `killCopies`, and it has lost at most `G.copyCount H` edges.
-/
#check free_killCopies -- H ≠ ⊥ → H.Free (G.killCopies H)
#check le_card_edgeFinset_killCopies
-- #G.edgeFinset - G.copyCount H ≤ #(G.killCopies H).edgeFinset

/-!
The triangle removal lemma is a far stronger statement: if a graph on `n` vertices
has few triangles, `o(n³)`, then it can be made triangle-free by deleting few edges,
`o(n²)`. In Mathlib a graph is `ε`-*far from triangle-free* if at least `ε n²` edges
must be deleted to make it triangle-free.
-/
#source FarFromTriangleFree

/-!
The lemma is proved by applying the regularity lemma, and then a *counting lemma*:
three parts that are pairwise uniform and dense span many triangles.
-/
#check triangle_counting
-- s, t, u pairwise dense and uniform → (1 - 2ε) ε³ #s #t #u ≤ #(G.cliqueFinset 3)

#check FarFromTriangleFree.le_card_cliqueFinset
-- G.FarFromTriangleFree ε → triangleRemovalBound ε * n ^ 3 ≤ #(G.cliqueFinset 3)

#check triangle_removal
-- few triangles → ∃ triangle-free G' ≤ G with less than ε * n ^ 2 edges removed

/-!
## Roth's Theorem

The triangle removal lemma has a striking application in number theory.

*Roth's theorem* says that a set of integers with positive density contains a
three-term arithmetic progression `a, a + d, a + 2d` with `d ≠ 0`. More precisely,
for every `ε > 0` and all large enough `n`, every subset of `{0, …, n − 1}` with at
least `εn` elements contains one. Mathlib phrases this as "is not `ThreeAPFree`".
-/
#check roth_3ap_theorem_nat
-- n large, A ⊆ range n, ε * n ≤ #A → ¬ThreeAPFree (A : Set ℕ)

/-!
The proof goes via the *corners theorem*: a dense set of points in the grid contains
a corner `(x, y), (x + d, y), (x, y + d)` with `d ≠ 0`. A corner-free set gives a
graph in which every edge lies in exactly one triangle (a *locally linear* graph),
and the removal lemma shows such graphs have few edges.
-/
#check corners_theorem_nat
#source LocallyLinear

#check EdgeDisjointTriangles.card_edgeFinset_le
-- G.EdgeDisjointTriangles → 3 * #(G.cliqueFinset 3) ≤ #G.edgeFinset

/-!
How many edges can a locally linear graph on `n` vertices have? The removal lemma
shows `o(n²)`, and Mathlib also has Behrend's construction, which gives a nearly
matching lower bound for this *Ruzsa–Szemerédi problem*.
-/
#check ruzsaSzemerediNumberNat_asymptotic_lower_bound
-- (fun n ↦ n ^ 2 * exp (-4 * √(log n))) =O[atTop] fun n ↦ ruzsaSzemerediNumberNat n

/-!
# Infinite Graphs *

Most of this guide deals with finite graphs or with infinite graphs through their
finite parts. We end with two results about the infinite structure of a graph.

## Kőnig's Lemma

*Kőnig's lemma* says that an infinite, connected, locally finite graph contains an
infinite path. Mathlib has the order-theoretic form of this result: in a (strongly
atomic) partial order in which each element is covered by finitely many elements, an
element with infinitely many elements above it starts an infinite chain
`b = f 0 ⋖ f 1 ⋖ f 2 ⋖ ⋯` of covering steps.
-/
#check exists_seq_covby_of_forall_covby_finite
-- finitely many covers, (Set.Ici b).Infinite → ∃ f, f 0 = b ∧ ∀ i, f i ⋖ f (i + 1)

/-!
Like the De Bruijn–Erdős theorem
([De Bruijn–Erdős Theorem](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-de-bruijn-erd-s-theorem))
and Hall's theorem for infinite graphs
([Hall's Marriage Theorem](https://jt496.github.io/GraphTheoryInLean/Theorems/#section-hall-s-marriage-theorem)),
this is a *compactness* argument, deducing an infinite object from finite
information.

## Ends

The *ends* of an infinite graph describe the different ways of going to infinity.
The usual definition is in terms of *rays*, or one-way infinite paths. Two rays are
*equivalent* if no finite set of vertices separates them: for every finite set `K`,
both rays have tails in the same component of the graph with `K` deleted. An end is
an equivalence class of rays.

Mathlib uses an equivalent definition that avoids rays. Write `G.ComponentCompl K`
for the set of components of `G - K`. A ray chooses, for each finite `K`, the
component of `G - K` containing a tail of the ray, and these choices are consistent:
if `K ⊆ L` then the component chosen for `L` lies inside the one chosen for `K`. Any
consistent choice of components is called a *direction*.
-/
#source ComponentCompl -- abbrev ComponentCompl := (G.induce Kᶜ).ConnectedComponent

/-- A *direction* of `G` chooses, for every finite set `K` of vertices, a component
`f K` of `G - K`, consistently: if `K ⊆ L` then `f L ⊆ f K`. -/
def IsDirection (f : (K : Finset V) → G.ComponentCompl K) : Prop :=
  ∀ ⦃K L : Finset V⦄, K ⊆ L → (f L : Set V) ⊆ f K

/-!
Equivalent rays give the same direction, and Diestel and Kühn showed that every
direction comes from a ray, so ends and directions are the same thing. Mathlib
defines the ends of `G` as its directions, but in the language of category theory.
`G.componentComplFunctor` is the functor sending each finite set `K` to
`G.ComponentCompl K`, and each inclusion `K ⊆ L` to the map `ComponentCompl.hom`
sending a component of `G - L` to the component of `G - K` that contains it. These
maps run from `L` to `K`, so the functor is defined on the opposite category
`(Finset V)ᵒᵖ`. A direction is then a *section* of this functor: an element of each
set, compatible with all of the maps.
-/
#check SimpleGraph.end -- Set ((K : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj K)

/-!
Unwinding the definitions, the elements of `G.end` are exactly the directions. (Here
`op K` is `K` regarded as an object of `(Finset V)ᵒᵖ`.)
-/
open CategoryTheory Opposite in
/-- The ends of `G`, as defined in Mathlib, are exactly its directions. -/
theorem mem_end_iff {f : (K : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj K} :
    f ∈ G.end ↔ G.IsDirection fun K => f (op K) := by
  constructor
  · intro hf K L hKL
    exact (ComponentCompl.hom_eq_iff_le _ (Finset.coe_subset.2 hKL) _).1
      (hf (opHomOfLE hKL))
  · intro hf K L h
    exact (ComponentCompl.hom_eq_iff_le _ (Finset.coe_subset.2 (leOfHom h.unop)) _).2
      (hf (leOfHom h.unop))

/-!
A finite graph has no ends, since the component chosen for `K = V` would be empty.
Kőnig's lemma reappears as the statement that every infinite, connected, locally
finite graph has at least one end. (Mathlib states connectivity as an instance
argument `[Fact G.Preconnected]`.)
-/
#check nonempty_ends_of_infinite
-- [G.LocallyFinite] [Fact G.Preconnected] [Infinite V] → G.end.Nonempty

/-!
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
For example, `pathNat₁` has exactly one end. Given a finite set `K`, choose `N` with
`K ⊆ [0, N]`. The translate `N + 1, N + 2, …` of `pathNat₁` avoids `K`, so it lies in
a single component of `G - K`. Each end chooses infinite components, and an infinite
component contains some `m > N`, and hence contains `N + 1`. So every end chooses the
component containing `N + 1`.
-/
example : Nat.card pathNat₁.end = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun ⟨e, he⟩ ⟨f, hf⟩ => Subtype.ext (funext fun K => ?_)⟩, ?_⟩
  · obtain ⟨N, hN⟩ := K.unop.finite_toSet.bddAbove
    let φ := (pathNat₁Translate (N + 1)).toHom
    have hφ (n : ℕ) : φ n = n + (N + 1) := rfl
    have hK (n : ℕ) : φ n ∉ K.unop := fun h => by
      have := hN h; rw [hφ] at this; grind
    -- every infinite component of `G - K` contains `N + 1`
    have key (C : pathNat₁.ComponentCompl K.unop) (hC : C.supp.Infinite) :
        N + 1 ∈ C := by
      obtain ⟨m, hmC, hm⟩ := hC.exists_gt N
      have h₁ : φ (m - (N + 1)) = m := by rw [hφ]; grind
      have h₂ : φ 0 = N + 1 := by rw [hφ]; grind
      exact h₂ ▸ ComponentCompl.mem_of_hom pathNat₁_connected.preconnected φ hK
        (h₁ ▸ hmC) 0
    exact ComponentCompl.pairwise_disjoint.eq (Set.not_disjoint_iff.2 ⟨_,
      key _ (end_componentCompl_infinite _ ⟨e, he⟩ K),
      key _ (end_componentCompl_infinite _ ⟨f, hf⟩ K)⟩)
  · have : Fact pathNat₁.Preconnected := ⟨pathNat₁_connected.preconnected⟩
    exact (nonempty_ends_of_infinite _).to_subtype

/-!
In the exercises we show that the grid `ℤ × ℤ` has exactly one end. Note that in
Lean this grid is the box product `hasse ℤ □  hasse ℤ`.
-/
end SimpleGraph
