import GraphTheoryInLean.C06_Cliques.C06_Cliques
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Partition
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
import Mathlib.Data.List.GetD
namespace SimpleGraph
/-!
A *proper colouring* of a graph assigns a colour to each vertex so that adjacent
vertices receive different colours, and the *chromatic number* is the least number of
colours that suffice. Colourings are among the most studied topics in graph theory.
Any clique needs as many colours as it has vertices, so the clique number is a lower
bound for the chromatic number, and the Mycielskian shows that this bound can be
arbitrarily bad.

In this chapter we study graph colourings (`Coloring`), colourability (`Colorable`),
the chromatic number (`chromaticNumber`) and bipartite graphs (`IsBipartite`). We
relate colourings to cliques and independent sets, showing that a finite graph has at
most `χ G * ⍺ G` vertices and that colourings of two graphs whose supports meet in a
clique can be amalgamated. We then colour some concrete graphs: blow-ups, box
products and hypercubes. We show that the chromatic number of the Mycielskian is
exactly one more than that of the original graph, which is what makes the clique
bound arbitrarily bad. We also look briefly at edge colourings.

Finally we turn to the *greedy* colouring algorithm. We first define it in a form
that is easy to reason about, using `Nat.find` and well-founded recursion, and use
this to prove that any locally finite graph on a countable vertex type with all
degrees at most `Δ` is `(Δ + 1)`-colourable. We look at the crown graph to see how
badly the greedy colouring can perform. We end by looking at how to make it more
efficient to run.

# Colourings

In Mathlib, a `γ`-colouring of `G` is a *graph homomorphism* from `G` to the complete
graph `⊤` on `γ`. Since all distinct pairs of vertices are adjacent in `⊤`, this
corresponds exactly to a proper `γ`-colouring.
-/
open Finset
section colorings
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

#source SimpleGraph.Coloring -- abbrev Coloring (α : Type v) := G →g completeGraph α

/-!
Adjacent vertices get different colours.
-/
#check Coloring.valid  -- C.valid : G.Adj u v → C u ≠ C v

/-!
The colour class of a colour `c` is the set of vertices coloured `c`.
-/
#check Coloring.colorClass -- C.colorClass c : Set V

/-!
Colour classes are independent sets.
-/
#check Coloring.isIndepSet_colorClass -- : G.IsIndepSet (C.colorClass c)

/-!
So a colouring is the same thing as a partition of the vertices into independent
sets, one for each colour. Mathlib makes this precise with `Coloring.toPartition` and
`partitionable_iff_colorable`.
-/
#check Coloring.toPartition -- (C : G.Coloring α) : G.Partition
#check partitionable_iff_colorable -- G.Partitionable n ↔ G.Colorable n

/-!
Any cycle graph can be `3`-coloured, and any even cycle can be `2`-coloured using
`Bool` as the set of colours. Colourings of concrete graphs can also be evaluated.
-/
#eval cycleGraph.tricoloring 7 (by decide) -- {0 ↦ 0, 1 ↦ 1, 2 ↦ 0, 3 ↦ 1,
                                           --         4 ↦ 0, 5 ↦ 1, 6 ↦ 2}

#eval cycleGraph.bicoloring_of_even 4 (by decide) -- {0 ↦ true, 1 ↦ false,
                                                  --      2 ↦ true, 3 ↦ false}

/-!
If `n : ℕ` then `G.Colorable n` says that `G` has a proper colouring with `n` colours
(using `Fin n`). Note the difference between the two notions: a `G.Coloring α` is
*data*, a specific colouring, whereas `G.Colorable n` is a `Prop` that only records
that some colouring exists (`Nonempty`). Inside a proof, `obtain ⟨C⟩ := h` recovers
a colouring `C` from `h : G.Colorable n`.
-/
example (n : ℕ) : G.Colorable n ↔ Nonempty (G.Coloring (Fin n)) := Iff.rfl

/-!
In the other direction, a colouring `C : G.Coloring α` with a finite type of colours
`α` shows that `G` is `Fintype.card α`-colourable.
-/
#check Coloring.colorable
-- [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α)

/-!
Note that `G.Colorable 0` holds iff `G` can be coloured with the colours `Fin 0`.
Since `Fin 0` has no elements, this is possible iff `G` has no vertices.
-/
#check colorable_zero_iff -- G.Colorable 0 ↔ IsEmpty V

/-!
If `G` is `n`-colourable and `n ≤ m`, then `G` is `m`-colourable.
-/
#check Colorable.mono

/-!
Since colourings are homomorphisms to `⊤`, we can compose them with any other
homomorphism: if `G →g G'` and `G'` is `n`-colourable then so is `G`.
-/
#check Colorable.of_hom -- (f : G →g G') (h : G'.Colorable n) : G.Colorable n

/-!
# Chromatic Number

The *chromatic number* of a graph `G` is the minimum number of colours needed to
colour `G`. In Mathlib, this is defined using `ℕ∞` which is `ℕ` together with `⊤`
(`∞`). So the chromatic number is the minimum `n` such that `G.Colorable n` holds, or
`⊤` if there is no such `n`.
-/
#source SimpleGraph.chromaticNumber  -- .. := ⨅ n ∈ Set.ofPred G.Colorable, (n : ℕ∞)

/-!
We introduce the standard `χ G` notation for the chromatic number of `G`.
-/
@[inherit_doc]
scoped notation "χ" => SimpleGraph.chromaticNumber

/-!
The basic tool for working with `χ G` is that, for `n : ℕ`, we have `χ G ≤ n` iff `G`
is `n`-colourable. Many proofs about the chromatic number start by rewriting with
this.
-/
#check chromaticNumber_le_iff_colorable -- χ G ≤ n ↔ G.Colorable n

/-!
The chromatic number is `n + 1` iff `G` is `(n + 1)`-colourable but not
`n`-colourable.
-/
#check chromaticNumber_eq_iff_colorable_not_colorable

/-!
If there is a homomorphism `G →g G'` then `χ G ≤ χ G'`. In particular a subgraph
has chromatic number at most that of the whole graph.
-/
#check chromaticNumber_mono_of_hom -- (f : G →g G') : χ G ≤ χ G'
#check chromaticNumber_mono -- (G' : SimpleGraph V) (h : G ≤ G') : χ G ≤ χ G'

/-!
Any graph on a finite set of vertices can be coloured with at most as many colours as
there are vertices.
-/
#check SimpleGraph.chromaticNumber_le_card  -- χ G ≤ Fintype.card V

/-- Any graph on a finite vertex type has finite chromatic number. -/
theorem chromaticNumber_ne_top_of_finite (G : SimpleGraph V) [Finite V] :
    χ G ≠ ⊤ :=
  chromaticNumber_ne_top_iff_exists.mpr ⟨_, G.colorable_chromaticNumber_of_fintype⟩

/-!
On an infinite vertex type the chromatic number can genuinely be `⊤`: the complete
graph on `ℕ` cannot be coloured with finitely many colours. Compare this with the
`ℕ`-valued clique number, for which `ω (⊤ : SimpleGraph ℕ) = 0` is a junk value.
-/
example : χ (⊤ : SimpleGraph ℕ) = ⊤ := chromaticNumber_top_eq_top_of_infinite ℕ

/-!
The complete graph on `Fin n` has chromatic number `n`.
-/
example (n : ℕ) : χ K[n] = n := by
  simp

/-!
# Colourings, Cliques and Independent Sets

Any `k`-clique in a graph requires at least `k` colours to colour it, so the clique
number of a graph is at most its chromatic number.
-/
#check cliqueNum_le_chromaticNumber
example {s : Finset V} (h : G.IsClique s) : #s ≤ χ G := h.card_le_chromaticNumber

/-!
So if `χ G < n` then `G` is `n`-clique-free.
-/
#check cliqueFree_of_chromaticNumber_lt

/-!
If a clique has at least as many vertices as there are colours, then every colour
appears on the clique.
-/
#check Coloring.surjOn_of_card_le_isClique

/-!
A proper colouring is injective on any clique: two distinct vertices of a clique are
adjacent, so they receive different colours. Since a colouring is a homomorphism,
this is a special case of `Hom.injOn_of_isClique` from
[Finite Cliques](https://jt496.github.io/GraphTheoryInLean/Cliques/#section-finite-cliques),
which dot notation finds for us.
-/
example {α : Type*} (c : G.Coloring α) {s : Set V} (hs : G.IsClique s) :
    Set.InjOn c s :=
  c.injOn_of_isClique hs

/-!
If `H` is not `n`-colourable and `G` is `n`-colourable then `G` cannot contain a copy
of `H`, e.g. a bipartite graph cannot contain a triangle.
-/
#check free_of_colorable

/-!
What can we say about maximally clique-free graphs? Suppose that `G` is
`(r + 1)`-clique-free but adding any edge creates an `(r + 1)`-clique. Then `G` is
`r`-colourable iff it is complete multipartite.
-/
#check colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree

/-!
A graph is *complete multipartite* if its vertices split into parts so that two
vertices are adjacent iff they lie in different parts. Mathlib defines this as
transitivity of non-adjacency in `G`. Non-adjacency is always reflexive (there are
no loops) and symmetric, so transitivity makes it an equivalence relation, and its
equivalence classes are the parts.
-/
#source IsCompleteMultipartite

/-!
Colour classes give a bound in the other direction, in terms of independent sets.
If `G` is `k`-colourable then its vertices are covered by `k` colour classes, each
an independent set of at most `⍺ G` vertices, so `G` has at most `k * ⍺ G` vertices.
No finiteness assumption is needed: if `V` is infinite then `Nat.card V` is the junk
value `0`, so the inequality holds trivially, and we dispose of this case first.
-/
theorem Colorable.natCard_le_mul_indepNum {k : ℕ} (h : G.Colorable k) :
    Nat.card V ≤ k * ⍺ G := by
  classical
  cases finite_or_infinite V with
  | inr => simp -- `Nat.card V` is the junk value `0`
  | inl =>
  have := Fintype.ofFinite V
  obtain ⟨C⟩ := h
  calc Nat.card V = ∑ i, #{v | C v = i} := by
        rw [Nat.card_eq_fintype_card, ← card_univ,
          card_eq_sum_card_fiberwise fun v _ => mem_univ (C v)]
    _ ≤ ∑ _ : Fin k, ⍺ G := sum_le_sum fun i _ => IsIndepSet.card_le_indepNum <| by
        simpa [Coloring.colorClass] using C.isIndepSet_colorClass i
    _ = k * ⍺ G := by simp

/-!
Taking `k = χ G` shows that a finite graph has at most `χ G * ⍺ G` vertices. As
before, the Lean statement needs no finiteness assumption, since it holds trivially
when `V` is infinite. Since `χ G` takes values in `ℕ∞`, the statement lives in `ℕ∞`:
the natural numbers `Nat.card V` and `⍺ G` are silently cast to `ℕ∞` (compare
[Counting in ℕ∞ : ENat.card](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-counting-in-enat-card)).

For finite `V` we cannot apply `Colorable.natCard_le_mul_indepNum` with `k = χ G`
directly, since `k` must be a natural number. This is a job for the `lift` tactic,
which moves a value from `ℕ∞` down to `ℕ` once we know that it is finite. Given a
proof that `χ G ≠ ⊤` (`chromaticNumber_ne_top_of_finite`),
`lift χ G to ℕ using … with k hk` introduces a natural number `k` with
`hk : ↑k = χ G` and replaces `χ G` by `↑k` in the goal. (We must name `k` here,
since `χ G` is an expression rather than a variable; when lifting a variable `x`,
`lift` reuses the name `x`.) Now `G` is `k`-colourable by
`chromaticNumber_le_iff_colorable`, and `exact_mod_cast` transfers the inequality
from `ℕ` to `ℕ∞`.
-/
theorem natCard_le_chromaticNumber_mul_indepNum : Nat.card V ≤ χ G * ⍺ G := by
  cases finite_or_infinite V with
  | inr => simp -- `Nat.card V` is the junk value `0`
  | inl =>
  lift χ G to ℕ using G.chromaticNumber_ne_top_of_finite with k hk
  exact_mod_cast (chromaticNumber_le_iff_colorable.mp hk.ge).natCard_le_mul_indepNum

/-!
## Amalgamating Colourings over a Clique *

Recall that the `support` of a graph is the set of vertices that are not isolated.
Suppose `G₁` and `G₂` share a vertex type and their supports meet in a set that is a
clique in both graphs. Then any colourings of `G₁` and `G₂` drawn from a common
palette can be amalgamated into a colouring of the union `G₁ ⊔ G₂` — a *clique-sum*.
On a clique both colourings are injective, so `Equiv.Perm.exists_extending_pair`
gives a permutation `σ` of the palette with `σ (c₂ x) = c₁ x` for every `x` in the
overlap. Then `c₁` on `G₁` and the recoloured `c₂` elsewhere agree on the overlap.

[Figure: Top left: $G_1$ coloured by $c_1$ and $G_2$ coloured by $c_2$; supports meet on $x$, $y$, $z$, and $c_1$ and $c_2$ disagree at $x$ and $y$. Bottom left: $G_1$ again, and $G_2$ recoloured by $\sigma \circ c_2$, where $\sigma$ swaps red and blue. Right: the glued colouring of $G_1 \sqcup G_2$](https://jt496.github.io/GraphTheoryInLean/figures/clique_sum_colouring.svg)
-/
theorem Colorable.sup_of_isClique_inter {G₁ G₂ : SimpleGraph V}
    (hs₁ : G₁.IsClique (G₁.support ∩ G₂.support))
    (hs₂ : G₂.IsClique (G₁.support ∩ G₂.support))
    {n : ℕ} (h₁ : G₁.Colorable n) (h₂ : G₂.Colorable n) :
    (G₁ ⊔ G₂).Colorable n := by
  classical
  obtain ⟨c₁⟩ := h₁
  obtain ⟨c₂⟩ := h₂
  let S := G₁.support ∩ G₂.support
  -- Both colourings are injective on the shared clique `S` (which is therefore
  -- finite), so a permutation `σ` of the palette carries `c₂` to `c₁` on `S`.
  have hinj₁ : Function.Injective (fun x : S => c₁ x) :=
    Set.injOn_iff_injective.1 (c₁.injOn_of_isClique hs₁)
  have hinj₂ : Function.Injective (fun x : S => c₂ x) :=
    Set.injOn_iff_injective.1 (c₂.injOn_of_isClique hs₂)
  have : Finite S := Finite.of_injective _ hinj₁
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : S => c₂ x) (fun x : S => c₁ x) hinj₂ hinj₁
  have hσkey : ∀ x ∈ S, σ (c₂ x) = c₁ x := fun x hx => hσ ⟨x, hx⟩
  -- The glued colouring: `c₁` on `G₁`'s support, the recoloured `c₂` elsewhere.
  let f : V → Fin n := fun x => if x ∈ G₁.support then c₁ x else σ (c₂ x)
  -- On `G₂`'s support, `f` coincides with the recoloured `c₂` (they agree on the
  -- shared clique).
  have key : ∀ {x}, x ∈ G₂.support → f x = σ (c₂ x) := fun {x} hx => by
    simp only [f]; split_ifs with hx1
    -- we use the `exacts` tactic to close the two goals
    exacts [(hσkey x ⟨hx1, hx⟩).symm, rfl]
  refine ⟨Coloring.mk f ?_⟩
  rintro a b (hab | hab)
  · -- An edge of `G₁`: both endpoints use `c₁`.
    simpa [f, hab.mem_support_left, hab.mem_support_right] using c₁.valid hab
  · -- An edge of `G₂`: both endpoints use the recoloured `c₂`.
    rw [key hab.mem_support_left, key hab.mem_support_right]
    exact fun h => c₂.valid hab (σ.injective h)

/-!
In particular if the supports of the two graphs share at most the single vertex `v`,
then any colourings of `G₁` and `G₂` with the same palette merge into a colouring of
`G₁ ⊔ G₂`. This is the special case of `sup_of_isClique_inter` where the overlap is a
subsingleton, hence vacuously a clique in each part.
-/
theorem Colorable.sup_of_subsingleton_inter {G₁ G₂ : SimpleGraph V}
    {v : V} (hmeet : G₁.support ∩ G₂.support ⊆ {v})
    {n : ℕ} (h₁ : G₁.Colorable n) (h₂ : G₂.Colorable n) :
    (G₁ ⊔ G₂).Colorable n := by
  have hsub := Set.subsingleton_of_subset_singleton hmeet
  exact Colorable.sup_of_isClique_inter (hsub.pairwise _) (hsub.pairwise _) h₁ h₂

/-!
This last result is the key step in colouring a graph block by block: in
[Colouring a Graph from its Blocks](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-colouring-a-graph-from-its-blocks)
we use it to show that if `n ≥ 1` and every block of a finite graph `G` is
`n`-colourable, then so is `G`.

# Bipartite Graphs

A graph is *bipartite* iff its vertices can be partitioned into two parts with no
edges within parts. In Mathlib this is defined in the obvious way via
`2`-colourability, so `G.IsBipartite` is exactly `G.Colorable 2`.
-/
#source IsBipartite -- abbrev IsBipartite (G : SimpleGraph V) : Prop := G.Colorable 2

/-!
Any complete bipartite graph is `2`-colourable (bipartite). Mathlib gives the natural
colouring, `CompleteBipartiteGraph.bicoloring`, which uses `Bool` as the set of
colours (`true` on the right part). By Mathlib's naming conventions it should be
called `completeBipartiteGraph.bicoloring` (compare `pathGraph.bicoloring`), so we
introduce that alias and use it for the rest of the guide.
-/
alias completeBipartiteGraph.bicoloring := CompleteBipartiteGraph.bicoloring

#check completeBipartiteGraph.bicoloring
  -- (V W : Type*) : (completeBipartiteGraph V W).Coloring Bool

/-!
By `Coloring.colorable`, this colouring shows that the complete bipartite graph is
bipartite. (Mathlib also has this as `IsBipartite.completeBipartiteGraph`.)
-/
example (V W : Type*) : (completeBipartiteGraph V W).IsBipartite :=
  (completeBipartiteGraph.bicoloring V W).colorable

/-!
When both parts are nonempty there is an edge, so the chromatic number is exactly
`2`. In general, a graph has chromatic number `2` iff it is bipartite and has an
edge.
-/
#check chromaticNumber_eq_two_iff -- χ G = 2 ↔ G.IsBipartite ∧ G ≠ ⊥

/-!
For example, colouring each vertex by its parity shows that the infinite path
`pathNat₁` has chromatic number `2`: an infinite graph can have finite chromatic
number.
-/
example : χ pathNat₁ = 2 :=
  chromaticNumber_eq_two_iff.2 ⟨(Coloring.mk (fun n => n % 2 == 0)
    (by rintro a b (rfl | rfl) <;> grind)).colorable,
    ne_bot_iff_exists_adj.2 ⟨0, 1, Or.inl rfl⟩⟩

/-!
We also have `IsBipartiteWith` which says that `G` is bipartite with all edges going
between the disjoint sets `s` and `t`. (Note that any isolated vertex can be in
either or neither of the parts.)
-/
#source IsBipartiteWith

/-!
For example, the complete bipartite graph is bipartite with parts the left and right
copies. (Mathlib also has this as `IsBipartiteWith.completeBipartiteGraph`.)
-/
example (V W : Type*) : (completeBipartiteGraph V W).IsBipartiteWith
    (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := by grind
  mem_of_adj {u v} h := by grind

/-!
Mathlib also shows that acyclic graphs, and in particular trees (see
[Acyclic Graphs, Trees and Forests](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-acyclic-graphs-trees-and-forests)),
are bipartite. The classical characterization, that a graph is bipartite iff it has
no odd cycles, is the subject of
[Odd Cycles and Bipartite Graphs](https://jt496.github.io/GraphTheoryInLean/Walks/#section-odd-cycles-and-bipartite-graphs).
-/
#check IsAcyclic.colorable_two -- (hG : G.IsAcyclic) : G.Colorable 2
#check IsTree.colorable_two -- (hG : G.IsTree) : G.Colorable 2

/-!
# Colouring Concrete Graphs

## Colouring Blow-ups

A graph `G` is `n`-colourable iff every blow-up of `G` with nonempty parts is
`n`-colourable. In one direction we pull a colouring back along the embedding
`Embedding.blowUp` of `G` into its blow-up (this is where we need the parts to be
nonempty); in the other we compose with the projection `Sigma.fst`, which is a
homomorphism from the blow-up to `G`.
-/
lemma blowUpGraph_colorable_iff {n : ℕ} {ι : Type*} {W : ι → Type*}
    (G : SimpleGraph ι) (f : ∀ i, W i) :
    (G.blowUpGraph W).Colorable n ↔ G.Colorable n :=
  ⟨fun h => h.of_hom (Embedding.blowUp G W f).toHom,
   fun h => h.of_hom ⟨Sigma.fst, fun h => by simpa [blowUpGraph_adj] using h⟩⟩

/-!
For example, Mathlib's complete multipartite graph `completeMultipartiteGraph W`,
with parts `W i`, is by definition the blow-up of the complete graph on the index
type. So when there are finitely many parts, all nonempty, its chromatic number is
the number of parts.
-/
example {ι : Type*} (W : ι → Type*) :
    completeMultipartiteGraph W = (⊤ : SimpleGraph ι).blowUpGraph W := rfl

#check completeMultipartiteGraph.chromaticNumber
  -- [Fintype ι] (f : ∀ i, W i) : χ (completeMultipartiteGraph W) = Fintype.card ι

/-!
## Colouring Box Products

A colouring `C` of `G □ H` restricts, along any fixed vertex of one factor, to a
colouring of the other factor with the same colours: `v ↦ C (v, w₀)` colours `G` and
`w ↦ C (v₀, w)` colours `H`.
-/
/-- The colouring of `G` induced by a colouring of `G □ H`. -/
def boxProdColoringLeft {α : Type*} (C : (G □ H).Coloring α) (w : W) :
    G.Coloring α :=
  C.comp <| boxProdLeft G H w

/-- The colouring of `H` induced by a colouring of `G □ H`. -/
def boxProdColoringRight {α : Type*} (C : (G □ H).Coloring α) (v : V) :
    H.Coloring α :=
  C.comp <| boxProdRight G H v

/-!
Conversely, given `k`-colourings of `G` and `H` we can `k`-colour `G □ H` as follows.
If `C₁ : G.Coloring (Fin k)` and `C₂ : H.Coloring (Fin k)` then `C : V × W → Fin k`
defined by `C (v, w) = C₁ v + C₂ w`, with addition modulo `k` in `Fin k`, is a valid
colouring of `G □ H`. Along an edge one coordinate is fixed, so the colours differ
because the colouring of the other factor is valid. (In the proof we need to
use `add_left/right_inj` in the final `simpa`s. These require `NeZero k`.)
-/
/-- The `k`-colouring of `G □ H` induced by `k`-colourings of `G` and `H`. -/
def boxProdColoring {k : ℕ} (C₁ : G.Coloring (Fin k)) (C₂ : H.Coloring (Fin k)) :
    (G □ H).Coloring (Fin k) :=
  Coloring.mk (fun x => C₁ x.1 + C₂ x.2) <| by
    rintro ⟨v, w⟩ ⟨v', w'⟩ (⟨hadj, rfl⟩ | ⟨hadj, rfl⟩)
    -- For these `simpa`s we need `NeZero k`, which holds since `C₁ v : Fin k`
      <;> have : NeZero k := ⟨by rintro rfl; exact (C₁ v).elim0⟩
    · simpa using C₁.valid hadj
    · simpa using C₂.valid hadj

/-- If `G` and `H` are both `k`-colourable then so is `G □ H`. -/
theorem Colorable.boxProd {k : ℕ} (h₁ : G.Colorable k) (h₂ : H.Colorable k) :
    (G □ H).Colorable k :=
  ⟨boxProdColoring h₁.some h₂.some⟩

/-!
Combining this with the restricted colourings above, if `G` and `H` are both nonempty
then `G □ H` is `k`-colourable iff both `G` and `H` are. (Nonemptiness is needed
here: if `H` has no vertices then neither does `G □ H`, so `G □ H` is colourable even
when `G` is not.)
-/
theorem colorable_boxProd_iff [Nonempty V] [Nonempty W] {k : ℕ} :
    (G □ H).Colorable k ↔ G.Colorable k ∧ H.Colorable k :=
  ⟨fun ⟨C⟩ => ⟨⟨boxProdColoringLeft C (Classical.arbitrary W)⟩,
      ⟨boxProdColoringRight C (Classical.arbitrary V)⟩⟩,
   fun h => h.1.boxProd h.2⟩

/-!
Hence if `G` and `H` are both nonempty then the chromatic number of `G □ H` is the
maximum of the chromatic numbers of `G` and `H`.

To prove an equality `a = b` in `ℕ∞` it suffices to show that `b ≤ m ↔ a ≤ m` for all
`m` (`eq_of_forall_ge_iff`). We then split into the cases `m = ⊤`, which is trivial,
and `m` a natural number, where `chromaticNumber_le_iff_colorable` turns both sides
into colourability statements.
-/
theorem chromaticNumber_boxProd [Nonempty V] [Nonempty W] :
    χ (G □ H) = max (χ G) (χ H) := by
  refine eq_of_forall_ge_iff fun m => ?_
  cases m with
  | top => simp
  | coe m => simp [chromaticNumber_le_iff_colorable, colorable_boxProd_iff]

/-!
Mathlib has the same result for the disjoint union `G ⊕g H`, where no nonemptiness
assumption is needed.
-/
#check chromaticNumber_sum -- χ (G ⊕g H) = max (χ G) (χ H)

/-!
## Colouring Hypercubes

Recall that `Q[n + 1]` is defined to be `Q[n] □ ⊤`, where `⊤` is the complete graph
on `Bool`. So `Colorable.boxProd` and induction on `n` show at once that every
hypercube is bipartite: `Q[0]` has no edges, and `⊤` on `Bool` is `2`-colourable.
-/
lemma hypercube_isBipartite (n : ℕ) : Q[n].IsBipartite := by
  induction n with
  | zero => exact ⟨Coloring.mk (fun _ => 0) (by simp [hypercube_zero])⟩
  | succ n ih => exact ih.boxProd (⊤ : SimpleGraph Bool).colorable_of_fintype

/-!
Behind this proof is an explicit colouring, but we cannot compute it from the proof:
`IsBipartite` is a `Prop`, and `Colorable.boxProd` picks its colourings with
`.some`. So we define the colouring directly. The box product colouring of
`Q[n] □ ⊤` gives `(v, b)` the colour of `v` plus `b`, modulo `2`. With `Bool` as the
colours, addition modulo `2` is `Bool.xor`, so we colour each vertex by the parity
of its coordinates.
-/
/-- The `Bool` colouring of `Q[n]` as a function. -/
def HypercubeVert.bool : {n : ℕ} → HypercubeVert n → Bool
  | 0, _ => false
  | _ + 1, (v, b) => v.bool ^^ b

/-!
This is a valid colouring.
-/
lemma HypercubeVert.bool_valid {n : ℕ} {v w : HypercubeVert n} (h : Q[n].Adj v w) :
    HypercubeVert.bool v ≠ HypercubeVert.bool w := by
  induction n with
  | zero => cases h
  | succ n ih =>
    rcases v; rcases w
    rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all [HypercubeVert.bool]

/-- The natural `Bool`-colouring of the hypercube `Q[n]`. -/
def hypercube.bicoloring (n : ℕ) : Q[n].Coloring Bool :=
  ⟨HypercubeVert.bool, HypercubeVert.bool_valid⟩

/-!
The hypercube is bipartite with the two parts being the sets of vertices with `bool`
values `true` and `false`.
-/
example (n : ℕ) : Q[n].IsBipartiteWith {v | v.bool} {v | ¬ v.bool} where
  disjoint := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext; simp
  mem_of_adj {u v} h := by
    have := HypercubeVert.bool_valid h
    by_cases u.bool <;> simp_all

/-!
Bipartite graphs are `3`-clique-free, hence `Q[n]` is `3`-clique-free.
-/
lemma hypercube_cliqueFree_three (n : ℕ) : Q[n].CliqueFree 3 :=
  (hypercube_isBipartite _).cliqueFree (by decide)

/-!
The `Bool`-colouring of `Q[4]` using `HypercubeVert.bool`.
-/
#eval (hypercube.bicoloring 4) -- {1111 ↦ false, 1110 ↦ true, ..., 0000 ↦ false}

end colorings

/-!
# Colouring Mycielskians

We now come to the main reason for defining the Mycielskian `mμ[G]` (`mycielskian`):
its chromatic number is exactly one more than that of `G`. Since `mμ[G]` is also
triangle-free whenever `G` is (`CliqueFree.mycielskian`), iterating the construction
gives triangle-free graphs of arbitrarily large chromatic number.

To show that `χ mμ[G] = χ G + 1` we will need to construct a `k`-colouring of `G`
from a `(k + 1)`-colouring of `mμ[G]` and also construct a `(k + 1)`-colouring of
`mμ[G]` from a `k`-colouring of `G`.

The basic idea is that if `mμ[G]` is `(k + 1)`-colourable then we can colour it with
the `k + 1` colours of `Fin (k + 1)` (i.e. `{0, 1, ..., k}`) in such a way that the
vertex `none` is coloured with colour `k`. Since `none` is adjacent to every vertex
in `Vᵣ` (the "right" copy of `V`), this ensures that no vertex in `Vᵣ` is coloured
`k`. We can then construct a `k`-colouring of `G` by colouring each vertex `v : V`
with the colour of `v ₗ`, if this doesn't equal `k`, and otherwise with the colour of
`v ᵣ` (which by construction is not `k`).

[Figure: The 3-colouring of $C_5$ induced from a 4-colouring of $mμ(C_5)$](https://jt496.github.io/GraphTheoryInLean/figures/mycielskian_coloring.svg)

Conversely given a `k`-colouring of `G` we can get a `(k + 1)`-colouring of `mμ[G]`
by colouring the "left" and "right" copies of `V` with the same colours as used by
their preimages in `G` and colouring `none` with the new colour `k`.

In `Fin (k + 1)` the top colour `k` is `Fin.last k`, and `Fin.castSucc` is the
inclusion of the colours `Fin k = {0, ..., k - 1}` into `Fin (k + 1)`. To move the
colour of `none` to `k` we use `recolorOfEquiv`, which recolours a colouring along a
bijection of the colours, in this case the transposition swapping `k` with the colour
of `none`: `Equiv.swap (Fin.last k) (c none)`.
-/
section mycielskian_and_edges
variable {V : Type*} {G : SimpleGraph V}

/-- Given any `(k + 1)`-colouring of `mμ[G]` this is the equivalent
`(k + 1)`-colouring in which the vertex `none` receives colour `k`. -/
def Coloring.mycielskianLast {k : ℕ} (c : mμ[G].Coloring (Fin (k + 1))) :
    mμ[G].Coloring (Fin (k + 1)) :=
  mμ[G].recolorOfEquiv (Equiv.swap (Fin.last k) (c none)) c

/-!
No vertex in the "right" copy of `V` is assigned the colour `k` in the
`Coloring.mycielskianLast`.
-/
lemma Coloring.mycielskianLast_ne_last {k : ℕ} (c : mμ[G].Coloring (Fin (k + 1)))
    {v : V} : c.mycielskianLast v ᵣ ≠ Fin.last k :=
  fun hf => c.mycielskianLast.valid (v := v ᵣ) (w := none)
             (by simp) (by rw [hf, Coloring.mycielskianLast]; simp)

/-- The natural `k`-colouring of `G` induced by a `(k + 1)`-colouring of `mμ[G]`. -/
def Coloring.ofMycielskian {k : ℕ} (c : mμ[G].Coloring (Fin (k + 1))) :
    G.Coloring (Fin k) where
  toFun v := if h : c.mycielskianLast v ₗ = Fin.last k
              then
                ⟨c.mycielskianLast v ᵣ, Fin.val_lt_last c.mycielskianLast_ne_last⟩
              else
                ⟨(c.mycielskianLast v ₗ), Fin.val_lt_last h⟩
  map_rel' := by
    intro a b hab hf
    -- the edge `a — b` of `G` gives three edges of `mμ[G]`
    have hll : mμ[G].Adj (a ₗ) (b ₗ) := by simpa using hab
    have hlr : mμ[G].Adj (a ₗ) (b ᵣ) := by simpa using hab
    have hrl : mμ[G].Adj (a ᵣ) (b ₗ) := by simpa using hab
    split_ifs at hf with ha hb hb
    · -- `a ₗ` and `b ₗ` both have colour `k`, but they are adjacent
      exact c.mycielskianLast.valid hll (ha.trans hb.symm)
    · -- `hf` says that the adjacent `a ᵣ` and `b ₗ` have the same colour
      exact c.mycielskianLast.valid hrl (by grind)
    · -- `hf` says that the adjacent `a ₗ` and `b ᵣ` have the same colour
      exact c.mycielskianLast.valid hlr (by grind)
    · -- `hf` says that the adjacent `a ₗ` and `b ₗ` have the same colour
      exact c.mycielskianLast.valid hll (by grind)

/-!
`Coloring.ofMycielskian` gives the harder direction; the easier direction is the
following colouring.
-/
/-- The `(k + 1)`-colouring of `mμ[G]` induced by a `k`-colouring of `G`. -/
def Coloring.mycielskian {k : ℕ} (c : G.Coloring (Fin k)) :
    mμ[G].Coloring (Fin (k + 1)) where
  toFun v :=
    match v with
    | none => Fin.last k
    | v ₗ | v ᵣ => (c v).castSucc
  map_rel' := by
    -- check all nine kinds of pair: an edge `none — v ᵣ` has the distinct colours
    -- `k` and `(c v).castSucc`; an edge between the copies has the colours of two
    -- adjacent vertices of `G`, which differ by `c.valid`; the other pairs are
    -- non-edges
    rintro (_ | v | v) (_ | w | w) hab <;>
      simp_all [c.valid, (Fin.castSucc_ne_last _).symm]

/-!
`G` is `k`-colourable iff `mμ[G]` is `(k + 1)`-colourable.
-/
lemma colorable_mycielskian_succ_iff (k : ℕ) :
    mμ[G].Colorable (k + 1) ↔ G.Colorable k := by
  constructor <;> intro ⟨c⟩
  · exact ⟨c.ofMycielskian⟩
  · exact ⟨c.mycielskian⟩

/-!
And so the chromatic number of `mμ[G]` is `χ G + 1`. We use the same strategy as for
`chromaticNumber_boxProd`: compare both sides with an arbitrary `m : ℕ∞`. When `m` is
a natural number we split further into the cases `m = 0` (neither side is at most
`0`, since `mμ[G]` has the vertex `none`) and `m = k + 1`, which is
`colorable_mycielskian_succ_iff`.
-/
/-- The chromatic number of the Mycielskian of `G`. -/
theorem chromaticNumber_mycielskian (G : SimpleGraph V) : χ mμ[G] = χ G + 1 := by
  refine eq_of_forall_ge_iff fun m => ?_
  cases m with
  | top => simp
  | coe m =>
    rcases m with _ | k
    · simp
    · rw [chromaticNumber_le_iff_colorable, colorable_mycielskian_succ_iff,
        Nat.cast_succ, ENat.add_le_add_iff_right ENat.one_ne_top,
        chromaticNumber_le_iff_colorable]

/-!
Notice that `chromaticNumber_mycielskian` needs no hypotheses at all. If `G` has no
finite colouring then both sides are `⊤` (in `ℕ∞` we have `⊤ + 1 = ⊤`), and if `V` is
empty then `χ G = 0` while `mμ[G]` is the single vertex `none`, so `χ mμ[G] = 1`.
Compare this with `cliqueNum_mycielskian_of_ne_bot`, which needs both `[Finite V]`
and `G ≠ ⊥`: the `ℕ`-valued clique number has the junk value `0` when there are
arbitrarily large cliques, and if `V` is nonempty then `ω ⊥ = 1` but `ω mμ[⊥] = 2`.

Since the Mycielskian is functorial (`Hom.mapMycielskian`), any homomorphism
`G →g H` lets us turn colourings of `mμ[H]` into colourings of `mμ[G]`, so
`χ mμ[G] ≤ χ mμ[H]`.
-/
#check Hom.mapMycielskian

example {W : Type*} {H : SimpleGraph W} (f : G →g H) (c : mμ[H].Coloring V) :
    mμ[G].Coloring V :=
  c.comp f.mapMycielskian

example {W : Type*} {H : SimpleGraph W} (f : G →g H) : χ mμ[G] ≤ χ mμ[H] :=
  chromaticNumber_mono_of_hom f.mapMycielskian

/-- The `n`-th iterated Mycielskian of `G` has chromatic number `χ G + n`. -/
theorem chromaticNumber_iterMycielskian (n : ℕ) : χ (mμ^n G) = χ G + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterMycielskian_succ, chromaticNumber_mycielskian, ih, add_assoc]
    -- `norm_cast` moves the casts `↑ : ℕ → ℕ∞` outwards and cancels them, here
    -- turning `↑n + 1` into `↑(n + 1)`; it is the tactic behind `exact_mod_cast`
    norm_cast

/-!
Since `K[2]` has chromatic number `2` (`chromaticNumber_top`), `mμ^n K[2]` has
chromatic number `n + 2`. (In particular `C[5] ≃g mμ[K[2]]` is `3`-chromatic and the
Grötzsch graph `mμ[C[5]]` is `4`-chromatic.)
-/
theorem chromaticNumber_iterMycielskian_completeGraph_two (n : ℕ) :
    χ (mμ^n K[2]) = n + 2 := by
  simp [chromaticNumber_iterMycielskian, add_comm]

/-!
Combining this with `cliqueNum_iterMycielskian_completeGraph_two` gives what we
promised, Mycielski's theorem: the graphs `mμ^n K[2]` all have clique number `2`,
but their chromatic numbers are unbounded. So the clique number can be an arbitrarily
bad lower bound for the chromatic number.
-/
/-- *Mycielski's theorem*: the nth-iterated Mycielskian of `K[2]` has clique number
`2` and chromatic number `n + 2`. -/
theorem mycielski (n : ℕ) : ω (mμ^n K[2]) = 2 ∧ χ (mμ^n K[2]) = n + 2 :=
  ⟨cliqueNum_iterMycielskian_completeGraph_two n,
    chromaticNumber_iterMycielskian_completeGraph_two n⟩

/-!
# Edge Colourings

So far we have coloured vertices. A *proper edge colouring* of `G` colours the edges
of `G` so that edges sharing an endpoint receive different colours. Mathlib has no
separate notion of this (its `EdgeLabeling` assigns labels to edges with no
properness condition), and we don't need one. Two edges share an endpoint exactly
when they are adjacent vertices of the line graph `L[G]` (`lineGraph`), so a proper
edge colouring of `G` with colours `γ` is just a colouring `L[G].Coloring γ`, and the
*chromatic index* `χ'(G)`, the least number of colours in a proper edge colouring, is
`χ L[G]`.

The edges at a vertex `v` pairwise share the endpoint `v`, so they form a clique in
`L[G]`. Hence the chromatic index is at least the degree of any vertex.
-/
theorem degree_le_chromaticNumber_lineGraph (v : V) [Fintype (G.neighborSet v)] :
    G.degree v ≤ χ L[G] := by
  -- the edges `s(v, w)` at `v`, as vertices of `L[G]`
  let f : G.neighborSet v ↪ G.edgeSet :=
    ⟨fun w => ⟨s(v, w), w.2⟩, fun _ _ h => Subtype.ext (Sym2.congr_right.mp
      (congrArg Subtype.val h))⟩
  have hc : L[G].IsClique (univ.map f : Finset G.edgeSet) := by
    simp only [coe_map, coe_univ, Set.image_univ]
    rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ hne
    exact ⟨hne, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  have := hc.card_le_chromaticNumber
  rwa [card_map, card_univ, card_neighborSet_eq_degree] at this

/-!
Taking `v` of maximum degree, the chromatic index of a finite graph is at least its
maximum degree `Δ(G)`.
-/
theorem maxDegree_le_chromaticNumber_lineGraph [Fintype V] [DecidableRel G.Adj] :
    G.maxDegree ≤ χ L[G] := by
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ G.degree_le_chromaticNumber_lineGraph v

end mycielskian_and_edges

/-!
Vizing's theorem
[Vizing 1964](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-vizing-1964)
says that this lower bound is almost tight: `χ'(G) ≤ Δ(G) + 1` for every finite graph
`G`, and Kőnig's line colouring theorem
[Kőnig 1916](https://jt496.github.io/GraphTheoryInLean/Appendix/#bib-konig-1916) says
that `χ'(G) = Δ(G)` for every finite bipartite graph `G`. Neither is in Mathlib yet.
The greedy bound of the next section, applied to `L[G]`, whose vertices have degree
at most `2 * Δ(G) - 2`, gives the much weaker `χ'(G) ≤ 2 * Δ(G) - 1`. (Mathlib is
also missing many other standard topics of colouring theory such as chromatic
polynomials and list colourings.)

# Greedy Colouring *

*Greedy colouring* means constructing a colouring one vertex at a time, choosing the
smallest valid colour at each step, i.e. for the current vertex `v`, the smallest
colour not used by any of the neighbours of `v` that we've already coloured. How many
colours this uses depends not on the degrees of the vertices but on the number of
neighbours that *precede* each vertex in the order in which we colour them, so we
start by defining this.

## Degree-less-than

In order to define the set of neighbours of a vertex `v` that are less than `v`, we
need some kind of ordering on the vertices. The simplest form this can take is an
instance of `LT` on the vertex type.
-/
section degreeLT
variable {V : Type*} (G : SimpleGraph V) [LT V]

/-- The set of neighbours of `v` that are less than `v`. -/
def neighborLTSet (v : V) : Set V := {u | u < v ∧ G.Adj v u}

@[simp]
lemma mem_neighborLTSet (v : V) (u : V) :
    u ∈ G.neighborLTSet v ↔ u < v ∧ G.Adj v u := Iff.rfl

/-!
The assumption that this set is finite is `Fintype (G.neighborLTSet v)`.
With this finiteness assumption we can define the `Finset` version of this set.
-/
/-- The neighbours of `v` that are less than `v` as a `Finset`. -/
def neighborLTFinset (v : V) [Fintype (G.neighborLTSet v)] : Finset V :=
  (G.neighborLTSet v).toFinset

@[simp]
lemma mem_neighborLTFinset (v : V) [Fintype (G.neighborLTSet v)] (u : V) :
    u ∈ G.neighborLTFinset v ↔ u < v ∧ G.Adj v u := Set.mem_toFinset

/-!
Finally the `degreeLT` is just the size of this finite set.
-/
/-- The number of neighbours of `v` that are less than `v`. -/
def degreeLT (v : V) [Fintype (G.neighborLTSet v)] : ℕ :=
  (G.neighborLTFinset v).card

end degreeLT

/-!
Recall from
[Finite Neighbourhoods](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-finite-neighbourhoods)
that `G.LocallyFinite` is an abbreviation for `∀ v, Fintype (G.neighborSet v)`: the
assumption that every vertex in a graph `G` has finitely many neighbours. We now need
its `LT` analogue: every vertex in `G` has finitely many *earlier* neighbours.
-/
abbrev LocallyLTFinite {V : Type*} [LT V] (G : SimpleGraph V) :=
  ∀ n, Fintype (G.neighborLTSet n)

/-!
## Simple Graphs on `ℕ`

If `G` is a graph with vertex type `ℕ` and decidable adjacency, then we get
`LocallyLTFinite` for free, since `G.neighborLTSet v` is a subset of the finite set
`{0, 1, …, v - 1}`: any vertex `v : ℕ` has at most `v` earlier neighbours! So for
now we will restrict our attention to such graphs, and to keep things simple we will
also use `ℕ` as our set of colours. (Later we will show how to easily extend our
greedy colourings to any constructively countable vertex type.)
-/
section greedy
variable (G : SimpleGraph ℕ) [DecidableRel G.Adj]

/-!
Any `SimpleGraph ℕ` with decidable adjacency is `LocallyLTFinite`.
-/
instance : G.LocallyLTFinite :=
  fun v => Fintype.ofFinset {u < v | G.Adj v u} (by simp [neighborLTSet])

/-!
Given an assignment `c` of colours to `{0, 1, ..., v - 1}`, we want to define the
colour of `v` as the smallest natural number that is not used by any of its earlier
neighbours. Rather than actually taking `c` to be a function defined only on
`{0, 1, ..., v - 1}`, we will instead take `c : ℕ → ℕ` but then ignore the values of
`c` at vertices `u ≥ v`.

So given `c : ℕ → ℕ` and a vertex `v : ℕ`, how should we define the greedy choice of
colour at `v`? The most direct route uses `Nat.find`: given a decidable predicate
`p : ℕ → Prop` and a proof that there exists an `n` such that `p n`, `Nat.find`
returns the least such `n`.
-/
#check Nat.find      -- Nat.find {p : ℕ → Prop} [DecidablePred p] (H : ∃ n, p n) : ℕ
#check Nat.find_spec -- .. (H : ∃ n, p n) : p (Nat.find H)
#check Nat.find_min  -- .. (H : ∃ n, p n) {m : ℕ} : m < Nat.find H → ¬p m
#check Nat.find_min' -- .. (H : ∃ n, p n) {m : ℕ} (h : p m) : Nat.find H ≤ m

/-!
To use this for the choice of colour at vertex `v`, we simply need to prove that
there is at least one natural number that is not used by any of the earlier
neighbours of `v`.
-/
lemma greedyChoice_exists (c : ℕ → ℕ) (v : ℕ) :
    ∃ x, x ∉ (G.neighborLTFinset v).image c :=
  ((G.neighborLTFinset v).image c).exists_notMem

/-- Given any `c : ℕ → ℕ` and a vertex `v : ℕ`, `G.greedyChoice c v` is the least
colour that is valid at `v` (in the sense that no earlier neighbour of `v` uses this
colour). -/
def greedyChoice (c : ℕ → ℕ) (v : ℕ) : ℕ := Nat.find (G.greedyChoice_exists c v)

/-!
The colour chosen at vertex `v` is at most the number of *distinct* colours used by
its earlier neighbours.
-/
lemma greedyChoice_le_card_image (c : ℕ → ℕ) (v : ℕ) :
    G.greedyChoice c v ≤ #((G.neighborLTFinset v).image c) := by
  have hsub : range (G.greedyChoice c v) ⊆ (G.neighborLTFinset v).image c :=
      fun u hu => not_not.mp <|
        Nat.find_min (G.greedyChoice_exists c v) (mem_range.mp hu)
  simpa using card_le_card hsub

/-!
The colour chosen at vertex `v` is never used by any earlier neighbour.
-/
lemma greedyChoice_ne_of_mem_neighborLTFinset (c : ℕ → ℕ) {v u : ℕ}
    (hu : u ∈ G.neighborLTFinset v) : G.greedyChoice c v ≠ c u :=
  fun hf =>
    Nat.find_spec (G.greedyChoice_exists c v) (mem_image.mpr ⟨u, hu, hf.symm⟩)

/-!
Finally, `greedyChoice c n` only inspects the partial colouring `c` on the earlier
neighbours of `n`, so two partial colourings that agree below `n` make the same
greedy choice at `n`.
-/
/-- `greedyChoice c n` only depends on the values of `c` below `n`. -/
lemma greedyChoice_congr {c₁ c₂ : ℕ → ℕ} {n : ℕ} (h : ∀ m < n, c₁ m = c₂ m) :
    G.greedyChoice c₁ n = G.greedyChoice c₂ n := by
  simp only [greedyChoice,
    image_congr fun m hm => h m ((G.mem_neighborLTFinset n m).mp hm).1]

/-!
[Figure: Left: a greedy colouring, with colours $0$, $1$, $2$ and $3$ drawn as red, blue, green and yellow. Right: for each vertex $n$, its earlier neighbours, the colours they forbid, and the least colour not forbidden](https://jt496.github.io/GraphTheoryInLean/figures/greedy.svg)

We will use `greedyChoice` to define a function `greedy` that will give us the greedy
colouring of `G` using *well-founded recursion* on `ℕ`: to colour a vertex `v` we
need to know the colours of the *earlier* vertices `u < v`, so the value of `greedy`
at `v` is defined in terms of its values at strictly smaller arguments.

Concretely, we feed `greedyChoice` the "partial colouring" function
`fun u ↦ if u < v then greedy u else 0`. The `if u < v` guard is what makes the
recursion well-founded: the recursive call `greedy u` occurs only in the `then`
branch, so it is guarded by `u < v`, which is exactly the fact Lean's termination
checker needs to discharge the proof that the call is at a strictly smaller argument.
The `0` in the `else` branch is just filler; its value is irrelevant, since
`greedyChoice` ignores the values of the partial colouring at `u ≥ v`.
-/
/-- The greedy `ℕ`-colouring of `G` as a function. -/
def greedy : ℕ → ℕ :=
  fun v => G.greedyChoice (fun u ↦ if u < v then (greedy u) else 0) v

/-!
Notice that we didn't need to prove that `greedy` is well-defined: by working over
`ℕ` Lean can automatically discharge the termination proof for us. (Under the hood
this is using `WellFounded.Nat.fix`.)
-/
#print greedy -- .. WellFounded.Nat.fix ..

/-!
Lean generates the defining equation `greedy.eq_1` for us, and we can unfold `greedy`
with `rw [greedy]`. Since the partial colouring used at `v` agrees with `greedy`
below `v`, `greedyChoice_congr` lets us drop the `if` altogether. Viewing
`G.greedyChoice` as a map from colourings `ℕ → ℕ` to colourings `ℕ → ℕ`, this says
that `greedy` is a fixed point of it: `greedy = G.greedyChoice greedy`.
-/
#check greedy.eq_1

lemma greedy_eq_greedyChoice (v : ℕ) : G.greedy v = G.greedyChoice G.greedy v := by
  rw [greedy]
  exact G.greedyChoice_congr fun u hu => ite_eq_left hu

/-!
The `greedy` colour of `v` is at most the number of distinct colours used by
`greedy` on the earlier neighbours of `v`.
-/
lemma greedy_le_card_image (v : ℕ) :
    G.greedy v ≤ #((G.neighborLTFinset v).image G.greedy) :=
  G.greedy_eq_greedyChoice v ▸ G.greedyChoice_le_card_image _ v

/-!
In particular the `greedy` colour of `v` is at most the number of earlier neighbours
of `v`, and hence is less than `degreeLT v + 1`.
-/
lemma greedy_lt (v : ℕ) : G.greedy v < G.degreeLT v + 1 :=
  Nat.lt_succ_iff.2 <| (G.greedy_le_card_image v).trans card_image_le

/-!
If `u < v` and `v` is adjacent to `u` then the `greedy` colour of `v` is not equal to
the `greedy` colour of `u`. (The line `variable {G} in` makes `G` an implicit
argument of this lemma only, since it can be read off from `hadj`.)
-/
variable {G} in
lemma Adj.greedy_ne_of_gt {u v : ℕ} (hadj : G.Adj v u) (h : u < v) :
    G.greedy v ≠ G.greedy u :=
  G.greedy_eq_greedyChoice v ▸
    G.greedyChoice_ne_of_mem_neighborLTFinset _ (by simp_all)

/-!
So any pair of adjacent vertices `u` and `v` in `G` receive different colours in the
greedy colouring.
-/
variable {G} in
lemma Adj.greedy_ne {u v : ℕ} (hadj : G.Adj u v) :
    G.greedy u ≠ G.greedy v := by
  rcases hadj.ne.lt_or_gt with h | h
  · exact (hadj.symm.greedy_ne_of_gt h).symm
  · exact hadj.greedy_ne_of_gt h

/-!
Together these results pin down the greedy colour exactly when the earlier neighbours
of `v` use precisely the colours `0, 1, ..., k - 1`: the colour of `v` is then `k`.
(This rather special lemma will be useful when we look at the crown graph later.)
-/
lemma greedy_eq_of_image_eq_range {v k : ℕ}
    (h : (G.neighborLTFinset v).image G.greedy = range k) : G.greedy v = k := by
  refine le_antisymm (by simpa [h] using G.greedy_le_card_image v) ?_
  by_contra! hlt
  obtain ⟨m, hm, hgm⟩ := mem_image.mp (h ▸ mem_range.2 hlt)
  exact ((G.mem_neighborLTFinset v m).1 hm).2.greedy_ne hgm.symm

/-!
## The Greedy Bound for Graphs on `ℕ`

With `greedy` in hand we can now formally define the greedy colouring of a graph
`G : SimpleGraph ℕ` as a `G.Coloring ℕ`.
-/
/-- The natural greedy `ℕ`-colouring of a graph `G : SimpleGraph ℕ`. -/
@[simps]
def greedyColoringNat : G.Coloring ℕ where
  toFun := G.greedy
  map_rel' := fun hadj hf => hadj.greedy_ne hf

/-- *The Greedy Colouring Bound:* Any graph on `ℕ` in which every vertex has at most
`Δ` earlier neighbours is `(Δ + 1)`-colourable. -/
theorem colorable_of_degreeLT_le {Δ : ℕ} (hdeg : ∀ v, G.degreeLT v ≤ Δ) :
    G.Colorable (Δ + 1) :=
  (colorable_iff_exists_bdd_nat_coloring _).2
    ⟨G.greedyColoringNat, fun v => (G.greedy_lt v).trans_le (by grind [hdeg v])⟩

/-!
This is stronger than the familiar bound `χ G ≤ Δ(G) + 1` in terms of the maximum
degree, since only *earlier* neighbours count. A finite graph whose vertices can be
ordered so that each has at most `d` earlier neighbours is called `d`-*degenerate*,
so this is the *degeneracy bound* `χ G ≤ d + 1`. As for the maximum degree bound,
Brooks' theorem
([Brooks' Theorem*](https://jt496.github.io/GraphTheoryInLean/Connectivity/#section-brooks-theorem))
shows that a connected graph needs all `Δ(G) + 1` colours only if it is a complete
graph or an odd cycle.

Our greedy colouring construction allows us to colour graphs on `ℕ`, for example
`pathNat₁`, the infinite path graph on `ℕ`, and `⊤`, the complete graph on `ℕ`.
-/
#eval pathNat₁.greedyColoringNat 9 -- 1

#eval (⊤ : SimpleGraph ℕ).greedyColoringNat 6 -- 6
end greedy

/-!
The `#eval`s above are deliberately timid: colouring vertex `6` of `⊤` is fine, but
vertex `10` would take several minutes. We will see why, and fix it, below.
-/

/-!
## Greedy Colouring vs. the Crown Graph

The classic example of a graph on which greedy colouring performs badly is the
balanced complete bipartite graph with the obvious perfect matching removed, known as
the *crown graph*, with its vertices ordered left, right, left, right, ...

We will look at its countably infinite incarnation. We will show that the greedy
colouring will use arbitrarily large colours, despite the graph being `2`-colourable.

[Figure: Left: the greedy colouring of `crownGraph`, gives vertex `n` colour `n / 2`. Right: an optimal `2`-colouring, by parity](https://jt496.github.io/GraphTheoryInLean/figures/crownGraph.svg)
-/

/-- The *crown graph* is the complete bipartite graph on even and odd naturals,
minus the perfect matching `2 * n ↦ 2 * n + 1`. -/
@[simps]
def crownGraph : SimpleGraph ℕ where
  Adj a b := a % 2 ≠ b % 2 ∧ a / 2 ≠ b / 2

instance : DecidableRel crownGraph.Adj := by
  unfold crownGraph; infer_instance

/-!
The earlier neighbours of `n` in `crownGraph` are `{1, 3, ..., n - 1}`, if `n` is
even, and `{0, 2, ..., n - 3}` if `n` is odd. We can see this in examples via `#eval`
and will prove it below.
-/
#eval crownGraph.neighborLTFinset 6 -- {1, 3, 5}
#eval crownGraph.neighborLTFinset 11 -- {0, 2, 4, 6, 8}

lemma crownGraph_neighborLTFinset (n : ℕ) :
    crownGraph.neighborLTFinset n = (range (n / 2)).image
        (fun k => if n % 2 = 0 then 2 * k + 1 else 2 * k) := by
  ext m
  simp only [mem_neighborLTFinset, crownGraph_adj, mem_image]
  constructor
  · intro ⟨hlt, hadj⟩
    exact ⟨m / 2, by grind⟩
  · grind

/-- The natural `2`-colouring of the `crownGraph`. -/
def crownGraph.twoColoring : crownGraph.Coloring (Fin 2) where
  toFun n := ⟨n % 2, by grind⟩
  map_rel' h := by simp_all

/-!
Colouring each vertex by its parity shows that `crownGraph` is bipartite.
-/
example : crownGraph.IsBipartite := crownGraph.twoColoring.colorable

/-!
The greedy colouring of `crownGraph` colours vertex `n` with colour `n / 2`. Given
that `degreeLT n = n / 2`, this is as bad as it could be! We can see an example via
`#eval`, and prove it below.
-/
#eval crownGraph.greedy 11 -- 5

theorem greedy_crownGraph_eq (n : ℕ) :
    crownGraph.greedy n = n / 2 := by
  -- we use strong induction on `n`
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- by induction the earlier neighbours of `n` use exactly the colours `< n / 2`
  refine crownGraph.greedy_eq_of_image_eq_range ?_
  ext c
  simp only [crownGraph_neighborLTFinset, mem_image, mem_range]
  grind

/-!
## Encodable Vertex Types

So far we have computed greedy colourings of graphs on `ℕ`. Suppose instead that we
have a graph `G : SimpleGraph V`, where `V` is countable. Informally we might say
"let the vertices of `G` be `v₀, v₁, v₂,…`", implicitly thinking of `G` as a
`SimpleGraph ℕ`. How can we formalize this in Lean?

Mathlib has the `Encodable` typeclass for constructively countable types (both finite
and infinite). It provides an `Encodable.encode` function that is an injection from
`V` to `ℕ` together with a partial inverse `Encodable.decode : ℕ → Option V`, which
satisfies `decode (encode v) = some v` for all `v : V`.
-/
#source Encodable
/-!
If `G` has an encodable vertex type then we can construct a greedy colouring of `G`
by first encoding its vertices in `ℕ` and then applying the greedy colouring
algorithm to `G` as a graph on `ℕ`.

One way to build the encoded graph is to push `G` forward along `Encodable.encode`
using `SimpleGraph.map`
([Maps](https://jt496.github.io/GraphTheoryInLean/Maps/#section-maps)).
-/
/-- The encoded graph defined via `SimpleGraph.map`. -/
@[simps!]
abbrev encodeMap {V : Type*} [Encodable V] (G : SimpleGraph V) :
    SimpleGraph ℕ := G.map Encodable.encode
/-!
This captures our informal construction above. (To be precise we are not
claiming that `G.encodeMap` is isomorphic to `G`: in general `encode` need not be
surjective, in which case `G.encodeMap` will be a copy of `G` with some additional
isolated vertices.) However, the `SimpleGraph.map` construction leaves us with
existential quantifiers in the adjacency relation.
-/
section encode
open Encodable
variable {V : Type*} [Encodable V]

example {a b : ℕ} {G : SimpleGraph V} : G.encodeMap.Adj a b ↔
    a ≠ b ∧ ∃ u v, G.Adj u v ∧ encode u = a ∧ encode v = b :=
  Iff.rfl

/-!
This prevents Lean from automatically deciding adjacency, even when `G.Adj` is
decidable. Since we need decidable adjacency to compute colourings, we instead build
the graph directly below using `Encodable.decode₂`, which preserves decidability.

Given `[Encodable V]` and `a : ℕ`, the function `Encodable.decode₂ V a` returns
`some u` such that `Encodable.encode u = a`, if such a `u : V` exists, and `none`
otherwise. We want `a b : ℕ` to be adjacent in the encoded graph iff there exist
adjacent `u v : V` with `Encodable.encode u = a` and `Encodable.encode v = b`, so we
can define it with a `match` statement on `Encodable.decode₂ V a` and
`Encodable.decode₂ V b`.
-/
#check decode₂

/-- The `SimpleGraph ℕ` corresponding to a graph `G : SimpleGraph V` with encodable
vertex type `V`, using `Encodable.decode₂` to preserve decidability of adjacency. -/
@[simps!]
protected def encode (G : SimpleGraph V) : SimpleGraph ℕ where
    Adj := fun a b =>
      match decode₂ V a, decode₂ V b with
      | some u, some v => G.Adj u v
      | _, _ => False
    symm := ⟨fun a b => by
      cases decode₂ V a <;> cases decode₂ V b <;> simp_all [Adj.symm]⟩
    loopless := ⟨fun a => by cases decode₂ V a <;> simp_all⟩

/-!
If `G` is a graph on an encodable vertex type with decidable adjacency then its
encoded graph also has decidable adjacency.
-/
instance {G : SimpleGraph V} [DecidableRel G.Adj] :
    DecidableRel (G.encode.Adj) := fun a b =>
  match ha : decode₂ V a, hb : decode₂ V b with
  | some u, some v => decidable_of_iff (G.Adj u v) (by rw [encode_adj, ha, hb])
  | none, _ => isFalse (by simp [encode_adj, ha])
  | _, none => isFalse (by simp [encode_adj, hb])

/-!
To transfer a greedy colouring of the graph `G.encode` back to a colouring of `G` we
use an embedding of `G` into `G.encode`.
-/
/-- The graph embedding of `G` into `G.encode` via `Encodable.encode`. -/
def Embedding.encode (G : SimpleGraph V) : G ↪g G.encode where
  toFun := Encodable.encode
  inj'  := encode_injective
  map_rel_iff' := by simp

/-!
We would like to prove the greedy colouring bound for any graph of bounded degree on
an `Encodable`, or even a plain `Countable`, vertex type.

We need a couple of simple lemmas. Firstly the earlier neighbourhood of an encoded
vertex in the encoded graph is contained in the image of the neighbourhood of that
vertex in the original graph under the encoding.
-/
lemma encode_neighborLTFinset_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    [G.LocallyFinite] (v : V) : G.encode.neighborLTFinset (encode v)
      ⊆ (G.neighborFinset v).image encode := by
  intro m hm
  have hadj := ((mem_neighborLTFinset ..).mp hm).2
  match hdm : decode₂ V m with
  | none => simp [hdm] at hadj
  | some u =>
    simp_all only [encodek₂, encode_adj, Finset.mem_image, mem_neighborFinset]
    exact ⟨_, hadj, decode₂_eq_some.mp hdm⟩

/-!
Hence the `degreeLT` of an encoded vertex is at most the degree of the original
vertex.
-/
lemma encode_degreeLT_le {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
    (v : V) : G.encode.degreeLT (encode v) ≤ G.degree v := by
  rw [degreeLT, degree]
  exact (card_le_card (encode_neighborLTFinset_subset v)).trans card_image_le

/-!
Using these lemmas we can now give the greedy `(Δ + 1)`-colouring of a graph with
maximum degree `Δ` on an encodable vertex type with decidable adjacency. (Note that
we don't actually refer to `maxDegree` below, since this would require a
mathematically unnecessary `Fintype V` instance. Instead we assume that all vertices
have finite neighbourhoods using `G.LocallyFinite` and a bound `Δ : ℕ` such that
`∀ v, G.degree v ≤ Δ`.)
-/
/-- The greedy `Fin (Δ + 1)` colouring of a graph with bounded degree `Δ`. -/
def greedyColoringFin {Δ : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    [G.LocallyFinite] (hdeg : ∀ v, G.degree v ≤ Δ) : G.Coloring (Fin (Δ + 1)) where
  toFun v := ⟨G.encode.greedy (encode v), by
    grind [G.encode_degreeLT_le v, G.encode.greedy_lt (encode v)]⟩
  map_rel' h := Fin.ne_of_val_ne ((Embedding.encode G).map_rel_iff.mpr h).greedy_ne

end encode

/-!
We can also prove (classically) that such a colouring exists without any assumptions
about encodability or decidability. For this a `Countable` instance, together with
the degree bound, suffices.
-/
theorem colorable_of_degree_le_of_countable {V : Type*} {G : SimpleGraph V} {Δ : ℕ}
    [Countable V] [G.LocallyFinite] (hdeg : ∀ v, G.degree v ≤ Δ) :
    G.Colorable (Δ + 1) := by
  classical
  rcases nonempty_encodable V with ⟨_⟩
  exact ⟨greedyColoringFin hdeg⟩

/-!
Later we will use the
[*De Bruijn–Erdős theorem*](https://jt496.github.io/GraphTheoryInLean/Subgraphs/#section-de-bruijn-erd-s-theorem)
to show that the countable assumption is also superfluous, but for this we need to
understand `Subgraph`s.

## Making `greedy` Fast *

Our definition of `greedy` has allowed us to prove the greedy colouring bound, but
how good is `greedy` as an *algorithm*? As promised, we now investigate why
evaluating it on dense graphs is so slow, and what to do about this. If you have no
interest in efficient algorithms or debugging, skip to
[Computing Colourings of Encodable Graphs](https://jt496.github.io/GraphTheoryInLean/Colorings/#section-computing-colourings-of-encodable-graphs):
all it needs from this section is that, by the end of it, `#eval` runs a fast
implementation of `greedy`.
-/
section evaluating
variable (G : SimpleGraph ℕ) [DecidableRel G.Adj]

/-!
### Debugging `greedy`

Lean provides the debugging tool `dbg_trace`: the expression `dbg_trace "msg"; e`
evaluates to `e`, printing `msg` as a side effect each time it is evaluated. We make
a version of `greedy` that prints a `*` each time it is called:
-/
/-- A copy of `greedy` that prints one `*` per call. -/
def greedyTraced : ℕ → ℕ :=
  fun v =>
    dbg_trace "*";
    G.greedyChoice (fun u ↦ if u < v then greedyTraced u else 0) v

/-!
Rather than printing thousands of stars and asking you to count them, we can capture
the trace inside Lean: `IO.FS.withIsolatedStreams` runs an `IO` action with its
output redirected into a `String`.
-/
/-- Evaluate `f ()`, capturing everything it `dbg_trace`s; return the value together
with the number of trace lines (here: the number of calls). -/
def withTraceCount {α : Type} (f : Unit → α) : IO (α × ℕ) := do
  let (out, a) ← IO.FS.withIsolatedStreams (IO.lazyPure f)
  -- each trace ends in a newline, so `splitOn` gives one more piece than there
  -- are traces
  return (a, (out.splitOn "\n").length - 1)

/-!
Before looking at the trace counts below, can you work out how bad it is?
-/
#eval do -- [1, 3, 13, 69, 431, 3103, 25341, 231689, 2345851]
  -- returns the number of calls made by `greedy` for
  -- the complete graph on `ℕ` when evaluated at `0, 1, ..., 8`
  let counts ← (List.range 9).mapM fun n =>
    withTraceCount fun _ => (⊤ : SimpleGraph ℕ).greedyTraced n
  return counts.map Prod.snd

/-!
So colouring vertex `8` of the complete graph, where `8` has eight earlier
neighbours, takes a truly unreasonable `2,345,851` calls! Even on the path
`pathNat₁`, where every vertex has at most one earlier neighbour, colouring vertex
`8` takes `46` calls. Why is it so bad?

Firstly, nothing is stored: each time the algorithm needs the colour of an earlier
vertex `m`, it recomputes `greedy m` completely from scratch. Secondly, `Nat.find`
finds the least valid colour by testing `0, 1, 2, ...` in turn, and every test
recomputes the finset `(G.neighborLTFinset v).image c`, thereby recomputing the
colour of *every* earlier neighbour of `v`.

Writing `C(n)` for the number of calls made when colouring `n`, and `c(n)` for the
colour that is chosen, we have `C(n) = 1 + (c(n) + 1) * ∑ C(m)`, where the sum runs
over all earlier neighbours `m` of `n` (there are `c(n) + 1` tests, each recomputing
the image). On the complete graph `⊤` we have `c(n) = n`, and so
`C(n) = 1 + (n + 1) * (C(0) + C(1) + ⋯ + C(n - 1))`, which grows faster than `n!`.
(On the path the colours alternate between `0` and `1`, and `C(n)` grows like
`2 ^ (n / 2)`.)

### Two Fixes: `Finset.min'` and Memoization

To deal with the second problem we compute the set of used colours *once*, and take
the smallest colour outside of this finite set. Naively this suggests we would need
to compute the minimum over an infinite set, namely
`ℕ \ (G.neighborLTFinset v).image c`, but that isn't the case.

The colours assigned by `c` to the earlier neighbours of `v` form the finite set
`(G.neighborLTFinset v).image c`. If this set has `k` elements then at least one of
the `k + 1` colours `0, ..., k` is not in this set, and hence the smallest valid
colour can be chosen as the minimum of the *finite* set:
`{0, ..., k} \ (G.neighborLTFinset v).image c`. We can do this using `Finset.min'`.

Given a nonempty `Finset` of natural numbers (or of any type with a linear order),
`Finset.min'` returns the smallest element of that `Finset`.
-/
#check Finset.min'     -- .. [LinearOrder α] → (s : Finset α) → s.Nonempty → α
#check Finset.min'_le  -- If `s : Finset α` and `x ∈ s` then `Finset.min' s ≤ x`
#check Finset.min'_mem -- If `s : Finset α` is nonempty then `Finset.min' s ∈ s`
/-!
We first formalize the statement that there exists a valid colour that is at most
`#((G.neighborLTFinset v).image c)` (our `k` from the discussion above).
-/
lemma greedyChoiceMin_sdiff_nonempty (c : ℕ → ℕ) (v : ℕ) :
    (range (#((G.neighborLTFinset v).image c) + 1)
      \ (G.neighborLTFinset v).image c).Nonempty :=
  card_pos.1 <| (le_card_sdiff ..).trans' (by simp)

/-!
We can now define a new version of `greedyChoice` using `Finset.min'`.
-/
/-- Given any `c : ℕ → ℕ` and a vertex `v : ℕ`, `G.greedyChoiceMin c v` is the least
colour that is valid at `v`, computed by removing the used colours from
`{0, ..., k}` (where `k` is the number of used colours) and taking the minimum. -/
def greedyChoiceMin (c : ℕ → ℕ) (v : ℕ) : ℕ := Finset.min'
  (range (#((G.neighborLTFinset v).image c) + 1) \ (G.neighborLTFinset v).image c)
    (G.greedyChoiceMin_sdiff_nonempty c v)

/-!
Our two definitions of the greedy choice agree.
-/
lemma greedyChoice_eq_greedyChoiceMin (c : ℕ → ℕ) (v : ℕ) :
    G.greedyChoice c v = G.greedyChoiceMin c v := by
  simp only [greedyChoiceMin, greedyChoice]
  apply le_antisymm
  · -- `greedyChoiceMin c v` is a valid colour, so `Nat.find` returns at most it
    exact Nat.find_min' _
      (mem_sdiff.mp (min'_mem _ (G.greedyChoiceMin_sdiff_nonempty c v))).2
  · -- `greedyChoice c v` lies in the finset that `greedyChoiceMin c v` minimizes
    apply min'_le
    rw [mem_sdiff, mem_range, Order.lt_add_one_iff]
    exact ⟨G.greedyChoice_le_card_image c v,
             Nat.find_spec (G.greedyChoice_exists c v)⟩

/-!
If we use `greedyChoiceMin` in place of `greedyChoice` in the definition of `greedy`,
each call evaluates the partial colouring only once per earlier neighbour. So the
recurrence loses its `(c(n) + 1)` factor and becomes `C(n) = 1 + ∑ C(m)`, summing
over the earlier neighbours `m` of `n`. On the path this is linear, but on the
complete graph it is still exponential because of the first problem:
`C(n) = 1 + C(0) + ⋯ + C(n - 1) = 2 ^ n`.

To fix the first problem we build a list of colours `[c 0, c 1, …, c (n - 1)]` by
ordinary structural recursion on `n`, so that each colour is computed exactly once,
and then look up the entry we need. This is a simple form of *memoization*.
-/
/-- The list of the first `n` greedy colours `[c 0, c 1, …, c (n - 1)]`,
built by structural recursion. -/
def greedyList : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := greedyList n
    l ++ [G.greedyChoiceMin (fun m => l.getD m 0) n]

/-!
The list `greedyList n` has length `n`.
-/
@[simp]
lemma length_greedyList (n : ℕ) : (G.greedyList n).length = n := by
  induction n <;> simp_all [greedyList]

/-!
We will use `List.getD` to read off the colour of vertex `n` from
`G.greedyList (n + 1)`.
-/
#check List.getD

/-- The memoized greedy colouring of `G`: build the list of the first `n + 1`
colours and look up the last entry. -/
def greedyMemo (n : ℕ) : ℕ := (G.greedyList (n + 1)).getD n 0

/-!
We now want to prove that this new version computes the same colours as `greedy`.
The list is correct: its `m`-th entry is `greedy m`. The induction is now the
ordinary one on the length of the list: extending the list by one entry
preserves the earlier entries (`List.getD_append`), and the new entry is the
correct greedy choice by `greedyChoice_congr`.
-/
lemma getD_greedyList {n m : ℕ} (hm : m < n) :
    (G.greedyList n).getD m 0 = G.greedy m := by
  induction n generalizing m with
  | zero => grind
  | succ n ih =>
    simp only [greedyList]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | rfl
    · rw [List.getD_append _ _ _ _ (by simpa using h)]
      exact ih h
    · rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [length_greedyList, Nat.sub_self, List.getD_cons_zero]
      rw [greedy_eq_greedyChoice, ← greedyChoice_eq_greedyChoiceMin]
      exact G.greedyChoice_congr fun k hk => ih hk

lemma greedyMemo_eq_greedy (n : ℕ) : G.greedyMemo n = G.greedy n :=
  G.getD_greedyList (Nat.lt_succ_self n)

/-!
Now each colour is computed exactly once, so colouring vertex `n` makes only `n + 1`
calls to `greedyChoiceMin`, whatever the graph. (You can check this by tracing
`greedyList` as we traced `greedy` above.) The number of calls is linear, although
the running time is not, since appending to a list and looking up its entries take
time proportional to its length.

Of our two fixes, memoization is the decisive one: even paired with the original
`Nat.find`-based `greedyChoice`, it would remove the exponential blow-up, since
every colour would still be computed only once. Using `greedyChoiceMin` as well
saves recomputing the image for every candidate colour, which matters for larger
graphs.

### Correct and Efficient: `csimp`

In `greedyMemo_eq_greedy` above we proved that both definitions compute the same
colouring: `greedy` has the cleanest definition and proofs due to Lean's support for
well-founded recursion on `ℕ` and the simplicity of `Nat.find`, but `greedyMemo` is
much more efficient. So which should we have chosen to implement?

It turns out that we don't have to choose! Lean's `csimp` attribute ("compiler
simp") registers a *proved* equation between two functions and makes the
compiler use the right-hand side whenever it compiles code that mentions the
left-hand side. So by marking the next result with `@[csimp]`, every definition and
proof below refers to `greedy`, while every `#eval` compiled from now on runs the
efficient memoized implementation.
-/
@[csimp]
theorem greedy_eq_greedyMemo : greedy = greedyMemo := by
  funext G _ n
  exact (G.greedyMemo_eq_greedy n).symm

/-!
Suddenly `greedy` is much faster!
-/
#eval (⊤ : SimpleGraph ℕ).greedy 200 -- 200

end evaluating

/-!
To be clear: `@[csimp]` rewrites `greedy` in code that is compiled *after* the
attribute is registered. Code compiled before it keeps its old, super-exponential
implementation. For example `greedyColoringNat` and `greedyColoringFin`, whose
`toFun` fields used the original `greedy` when they were defined, are still slow.
(This is why the computable colourings of the next section are defined only now, and
directly in terms of our new, efficient version of `greedy`.)
-/

/-!
## Computing Colourings of Encodable Graphs

With `greedy` now faster, the same construction as `greedyColoringFin` gives
computable greedy colourings of graphs on any encodable vertex type with decidable
adjacency.
-/
/-- The natural greedy `ℕ`-colouring of a graph `G : SimpleGraph V` on an `Encodable`
vertex type via its `Encodable` instance. -/
@[simps]
def greedyColoring {V : Type*} [Encodable V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.Coloring ℕ where
  toFun v := G.encode.greedy (Encodable.encode v)
  map_rel' h := ((Embedding.encode G).map_rel_iff.mpr h).greedy_ne

/-!
Most finite and countably infinite types have `Encodable` instances in Mathlib, but
for `ZMod n` and our Mycielskian and hypercube vertex types we need to provide them
ourselves. Each of these types is defined by cases or recursion on `n` (`ZMod 0` is
`ℤ` and `ZMod (n + 1)` is `Fin (n + 1)`), and instance search does not unfold such
definitions. So we unfold them by hand and let `infer_instance` handle each case: the
same pattern as the `DecidableEq` and `Fintype` instances for `HypercubeVert n` in
[Computations with Hypercubes](https://jt496.github.io/GraphTheoryInLean/Decidability___-Finiteness-and-Degrees/#section-computations-with-hypercubes).
-/
instance (n : ℕ) : Encodable (ZMod n) := by
  cases n <;> unfold ZMod <;> infer_instance

instance iterMycielskianEncodable {V : Type*} [Encodable V] (n : ℕ) :
    Encodable (mμᵥ^n V) := by
  induction n <;> unfold MycielskianVert <;> infer_instance

instance hypercubeEncodable (n : ℕ) : Encodable (HypercubeVert n) := by
  induction n <;> unfold HypercubeVert <;> infer_instance

/-!
We can now compute greedy colourings of many concrete graphs:
`K₇, C₇, K₅,₅, paleyGraph₁₇, Q₄, mμ(C₅), mμ⁴(C₅)`.
-/
#eval K[7].greedyColoring -- {0 ↦ 0, 1 ↦ 1, 2 ↦ 2, 3 ↦ 3, 4 ↦ 4, 5 ↦ 5, 6 ↦ 6}

#eval C[7].greedyColoring  -- {0 ↦ 0, 1 ↦ 1, 2 ↦ 0, 3 ↦ 1, 4 ↦ 0, 5 ↦ 1, 6 ↦ 2}

#eval K[5, 5].greedyColoring -- {Sum.inl 0 ↦ 0, Sum.inl 1 ↦ 0, ..., Sum.inr 4 ↦ 1}

#eval (paleyGraph (ZMod 17)).greedyColoring -- {0 ↦ 0, ..., 11 ↦ 5, ..., 16 ↦ 4}

#eval Q[4].greedyColoring  -- {1111 ↦ 0, 1110 ↦ 1, ..., 0001 ↦ 1, 0000 ↦ 0}

#eval mμ[C[5]].greedyColoring -- {∗ ↦ 0, 0ₗ ↦ 0, ..., 3ₗ ↦ 2, ..., 4ᵣ ↦ 1}

#eval (mμ^4 C[5]).greedyColoring -- {∗ ↦ 0, ∗ₗ ↦ 0, ∗ₗₗ ↦ 0, ∗ₗₗₗ ↦ 0,..., 4ᵣᵣᵣᵣ ↦ 1}

/-!
Unlike on the crown graph, `greedy` does well on all of these examples: each
colouring above is optimal. For instance the colouring of `mμ^4 C[5]` uses the
colours `0, ..., 6`, and since `χ C[5] = 3`, `chromaticNumber_iterMycielskian` shows
that `7` colours are needed. Similarly the `6` colours used for
`paleyGraph (ZMod 17)` are optimal: its independence number is `3` (see the exercises
of [Cliques](https://jt496.github.io/GraphTheoryInLean/Cliques/#chapter-cliques)), so
`natCard_le_chromaticNumber_mul_indepNum` gives `17 ≤ χ (paleyGraph (ZMod 17)) * 3`,
forcing at least `6` colours.

Now that `greedy` is faster we can also evaluate it much further along the crown
graph.
-/
#eval crownGraph.greedy 101 -- 50

end SimpleGraph
